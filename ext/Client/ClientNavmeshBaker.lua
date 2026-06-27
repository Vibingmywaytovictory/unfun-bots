---@class ClientNavmeshBaker
---@overload fun():ClientNavmeshBaker
ClientNavmeshBaker = class('ClientNavmeshBaker')

-- =============================================================================
-- Offline navmesh baker (client side).
--
-- VU only exposes raycasting on the client, so the actual world probing has to
-- happen here. This module performs a flood-fill over a horizontal grid: starting
-- from a set of known-walkable seed cells (the existing trace waypoints, or the
-- local player's position as a fallback) it probes each candidate cell with a
-- downward "find the floor" raycast plus an upward "is there standing room"
-- raycast, classifies it as walkable / blocked, and enqueues its neighbours.
--
-- The result is a 2.5D voxel grid keyed by (gx, gz, gy) so stacked surfaces
-- (bridges, multiple building floors) stay distinct. Cells are streamed to the
-- server in batches where they are persisted into the mod database, next to the
-- per-map trace tables.
--
-- This is an offline authoring tool: it is armed from the F12 settings UI
-- (Config.DebugBakeNavmesh) and driven by the `BakeNavmesh <start|stop|save|
-- clear|status>` console command. It is intentionally not run during normal play.
-- =============================================================================

require('__shared/Config')

---@type Logger
local m_Logger = Logger('ClientNavmeshBaker', Debug.Client.NODEEDITOR)
---@type Utilities
local m_Utilities = require('__shared/Utilities')
---@type ClientNodeEditor
local m_ClientNodeEditor = require('ClientNodeEditor')

-- Bake-state machine.
local BakeState = {
	Idle = 0,    -- armed but not sweeping
	Running = 1, -- actively flood-filling
	Done = 2,    -- frontier exhausted, ready to save
}

function ClientNavmeshBaker:__init()
	self.m_EventsReady = false

	-- Whether the subsystem is armed (mirrors Config.DebugBakeNavmesh).
	self.m_Armed = false

	-- Seed waypoints received from the server (same data the node editor uses).
	self.m_SeedWaypoints = {}
	self.m_RequestDataSent = false
	-- True if the last bake seeded from waypoints; false if it fell back to player position.
	self.m_SeededFromWaypoints = true

	-- Auto-start handling: when the toggle is enabled we kick off the bake on our
	-- own once seed data has had a moment to arrive, so no console command is needed.
	self.m_AutoStartPending = false
	self.m_AutoStartTimer = 0.0
	self.m_SeedRequestTimer = 0.0

	-- Streaming-save state. The save is spread across frames so a large mesh does not
	-- flood the network buffer (which would kick the client).
	self.m_Saving = false
	self.m_SaveQueue = {}
	self.m_SaveCursor = 1
	self.m_SaveTimer = 0.0

	-- The cell size of the mesh currently in memory (snapshotted by a bake or a load), so
	-- grid math matches the cells regardless of the live Config slider. nil = use Config.
	self.m_ActiveCellSize = nil

	-- Editor state.
	self.m_EditorActive = false                 -- mirrors Config.NavmeshEditor
	self.m_EditMode = false                      -- ALT toggles brush interaction
	self.m_Tool = 'paint'                        -- 'paint' | 'erase' | 'box'
	self.m_BrushRadius = Registry.NAVMESH.BRUSH_DEFAULT
	self.m_BrushHit = nil                        -- cached raycast hit position for the cursor
	self.m_BoxCornerA = nil                      -- first corner (box tool)
	self.m_FireLevel = 0.0                       -- LMB level captured in the input hook
	self.m_FireWasDown = false
	self.m_BrushTimer = 0.0
	self.m_CurrentStroke = nil                   -- in-progress edit, pushed to undo on release
	self.m_UndoStack = {}
	self.m_UnsavedEdits = 0
	-- True while the WebUI (F12 menu, settings, commo-rose) has the cursor. The editor
	-- suspends itself then so it never fights the menu for input.
	self.m_UiCapturing = false
	-- Client-load state (editor pulls the saved mesh from the server).
	self.m_Loading = false

	self:ResetBake()
end

-- Reset all per-bake working data.
function ClientNavmeshBaker:ResetBake()
	self.m_State = BakeState.Idle

	-- Walkable cells: key "gx:gz:gy" -> { x, y, z, gx, gz, gy }.
	self.m_Cells = {}
	-- Visited set (walkable or blocked): key -> true. Prevents re-probing.
	self.m_Visited = {}
	-- Frontier queue of candidate cells to probe: { gx, gz, expectedY }.
	self.m_Frontier = {}
	self.m_FrontierHead = 1

	self.m_WalkableCount = 0
	self.m_BlockedCount = 0
	self.m_TickTimer = 0.0

	-- Bounding index: spatial hash of seed positions, used to keep the flood-fill within
	-- m_BoundRadius meters of a waypoint (so it cannot run away across the whole map).
	-- Snapshotted at bake start; bucket size equals the radius. 0 = unbounded.
	self.m_SeedBuckets = {}
	self.m_BoundRadius = 0.0

	-- Whether this bake's result has already been auto-saved on completion.
	self.m_AutoSaved = false

	-- Overlay draw buffers (double-buffered, node-editor style): the heavy windowed
	-- build happens in the pre-sim pass and only swaps these into place, so OnUIDrawHud
	-- just iterates and renders them with zero computation.
	self.m_DrawNodes = {}
	self.m_DrawLines = {}
	self.m_DrawRebuildTimer = 0.0
	self.m_LastDrawCellKey = nil
end

-- =============================================
-- Registration / config
-- =============================================

-- Called from the client init once the (server-driven) console environment is up,
-- alongside the node editor's own registration.
function ClientNavmeshBaker:OnRegisterEvents()
	if self.m_EventsReady then
		return
	end

	Console:Register('BakeNavmesh',
		'<start|stop|save|clear|status> - Control the offline navmesh baker', self, self.OnConsoleCommand)

	-- Re-use the node editor's data feed to seed the bake from existing waypoints.
	-- VEXT allows multiple subscribers to the same NetEvent, so this is additive.
	NetEvents:Subscribe('ClientNodeEditor:RevieveNodes', self, self.OnReceiveNodes)

	-- Editor: navmesh streamed back from the server.
	NetEvents:Subscribe('Navmesh:LoadBegin', self, self.OnLoadBegin)
	NetEvents:Subscribe('Navmesh:LoadBatch', self, self.OnLoadBatch)
	NetEvents:Subscribe('Navmesh:LoadCommit', self, self.OnLoadCommit)

	self.m_EventsReady = true
end

-- Read the armed-state from the live config every settings change / tick. Cheap.
function ClientNavmeshBaker:_SyncArmedState()
	local s_ShouldBeArmed = Config.DebugBakeNavmesh == true

	if s_ShouldBeArmed == self.m_Armed then
		return
	end

	self.m_Armed = s_ShouldBeArmed

	if self.m_Armed then
		m_Logger:Write('Navmesh baker enabled. Baking will start automatically...')
		-- Request fresh seed data and queue an automatic start.
		self.m_RequestDataSent = false
		self.m_AutoStartPending = true
		self.m_AutoStartTimer = 0.0
		self.m_SeedRequestTimer = 0.0
	else
		m_Logger:Write('Navmesh baker disabled.')
		self.m_AutoStartPending = false
		if self.m_State == BakeState.Running then
			self.m_State = BakeState.Idle
		end
	end
end

-- =============================================
-- Console command
-- =============================================

---@param p_Args string[]|string
function ClientNavmeshBaker:OnConsoleCommand(p_Args)
	local s_Action = p_Args
	if type(p_Args) == 'table' then
		s_Action = p_Args[1]
	end
	s_Action = tostring(s_Action or ''):lower()

	if s_Action == 'start' then
		self:StartBake()
	elseif s_Action == 'stop' then
		self:StopBake()
	elseif s_Action == 'save' then
		self:SaveBake()
	elseif s_Action == 'clear' then
		self:ResetBake()
		m_Logger:Write('Navmesh bake cleared.')
	elseif s_Action == 'status' then
		self:PrintStatus()
	else
		m_Logger:Write('Usage: BakeNavmesh <start|stop|save|clear|status>')
	end
end

function ClientNavmeshBaker:PrintStatus()
	local s_StateName = 'Idle'
	if self.m_State == BakeState.Running then
		s_StateName = 'Running'
	elseif self.m_State == BakeState.Done then
		s_StateName = 'Done'
	end

	m_Logger:Write(string.format(
		'Navmesh baker: armed=%s state=%s walkable=%d blocked=%d frontier=%d',
		tostring(self.m_Armed), s_StateName, self.m_WalkableCount, self.m_BlockedCount,
		(#self.m_Frontier - self.m_FrontierHead + 1)))
end

-- =============================================
-- Bake control
-- =============================================

function ClientNavmeshBaker:StartBake()
	if not self.m_Armed then
		m_Logger:Write('Enable the Navmesh Baker setting (Trace category) first.')
		return false
	end

	self:ResetBake()

	local s_Seeds = self:_GatherSeeds()
	if #s_Seeds == 0 then
		m_Logger:Write('No seeds found yet. Need a trace or a living player to seed from.')
		return false
	end

	-- Snapshot the bound radius for this whole bake and build the spatial index.
	self.m_ActiveCellSize = Config.NavmeshCellSize
	self.m_BoundRadius = self:_ConfigBoundRadius()
	self:_BuildBoundIndex(s_Seeds)

	-- Seed the frontier.
	local s_Count = 0
	for l_Index = 1, #s_Seeds do
		local l_Pos = s_Seeds[l_Index]
		local s_Gx, s_Gz = self:_WorldToGrid(l_Pos.x, l_Pos.z)
		-- Seeds have no parent, so they are exempt from the step check (fromY = nil).
		if self:_EnqueueCell(s_Gx, s_Gz, l_Pos.y, nil) then
			s_Count = s_Count + 1
		end
	end

	self.m_State = BakeState.Running
	local s_BoundText = self.m_BoundRadius > 0 and (self.m_BoundRadius .. 'm bound') or 'no bound'
	m_Logger:Write('Navmesh bake started with ' .. tostring(s_Count) .. ' seed cells (' .. s_BoundText .. ').')
	return true
end

function ClientNavmeshBaker:StopBake()
	if self.m_State == BakeState.Running then
		self.m_State = BakeState.Idle
		m_Logger:Write('Navmesh bake paused. ' .. tostring(self.m_WalkableCount) .. ' walkable cells so far.')
	end
end

-- Gather the seed positions for this bake (existing trace waypoints, or the local
-- player's feet as a fallback). These both seed the flood-fill and define the bound.
---@return Vec3[]
function ClientNavmeshBaker:_GatherSeeds()
	local s_Seeds = {}

	-- Prefer the existing trace waypoints: they are known-walkable ground truth.
	for l_Index = 1, #self.m_SeedWaypoints do
		local l_Wp = self.m_SeedWaypoints[l_Index]
		if l_Wp ~= nil and l_Wp.Position ~= nil then
			s_Seeds[#s_Seeds + 1] = l_Wp.Position
		end
	end

	if #s_Seeds > 0 then
		self.m_SeededFromWaypoints = true
		m_Logger:Write('Seeding navmesh from ' .. tostring(#s_Seeds) .. ' waypoints.')
		return s_Seeds
	end

	-- Fallback: the local player's feet. This only covers the area around where you are
	-- standing (usually spawn), so it is a last resort when no waypoints are available.
	self.m_SeededFromWaypoints = false
	local s_Player = PlayerManager:GetLocalPlayer()
	if s_Player ~= nil and s_Player.soldier ~= nil and s_Player.soldier.worldTransform ~= nil then
		s_Seeds[#s_Seeds + 1] = s_Player.soldier.worldTransform.trans:Clone()
		m_Logger:Warning('No waypoints received - seeding from player position only (spawn area).')
	end

	return s_Seeds
end

-- Bound radius (meters) from config, falling back to the registry default. 0 = unbounded.
function ClientNavmeshBaker:_ConfigBoundRadius()
	local s_Radius = Config.NavmeshBoundRadius
	if s_Radius == nil then
		s_Radius = Registry.NAVMESH.BOUND_RADIUS
	end
	return s_Radius
end

-- Build a spatial hash of the seed positions, bucketed at the bound radius. Because the
-- bucket size equals the radius, any seed within the radius of a point is guaranteed to
-- live in the point's own bucket or one of its 8 neighbours.
---@param p_Seeds Vec3[]
function ClientNavmeshBaker:_BuildBoundIndex(p_Seeds)
	self.m_SeedBuckets = {}

	if self.m_BoundRadius <= 0 then
		return -- unbounded; nothing to index
	end

	local s_BucketSize = self.m_BoundRadius
	for l_Index = 1, #p_Seeds do
		local l_Pos = p_Seeds[l_Index]
		local s_Bx = math.floor(l_Pos.x / s_BucketSize)
		local s_Bz = math.floor(l_Pos.z / s_BucketSize)
		local s_Key = s_Bx .. ':' .. s_Bz
		local s_Bucket = self.m_SeedBuckets[s_Key]
		if s_Bucket == nil then
			s_Bucket = {}
			self.m_SeedBuckets[s_Key] = s_Bucket
		end
		s_Bucket[#s_Bucket + 1] = { x = l_Pos.x, z = l_Pos.z }
	end
end

-- True if the cell is within the bound radius (horizontally) of any seed waypoint.
---@param p_Gx integer
---@param p_Gz integer
---@return boolean
function ClientNavmeshBaker:_IsWithinBound(p_Gx, p_Gz)
	if self.m_BoundRadius <= 0 then
		return true
	end

	local s_Wx, s_Wz = self:_GridToWorldCenter(p_Gx, p_Gz)
	local s_BucketSize = self.m_BoundRadius
	local s_Bx = math.floor(s_Wx / s_BucketSize)
	local s_Bz = math.floor(s_Wz / s_BucketSize)
	local s_R2 = self.m_BoundRadius * self.m_BoundRadius

	for l_Dx = -1, 1 do
		for l_Dz = -1, 1 do
			local s_Bucket = self.m_SeedBuckets[(s_Bx + l_Dx) .. ':' .. (s_Bz + l_Dz)]
			if s_Bucket ~= nil then
				for l_Index = 1, #s_Bucket do
					local s_Dx = s_Wx - s_Bucket[l_Index].x
					local s_Dz = s_Wz - s_Bucket[l_Index].z
					if (s_Dx * s_Dx + s_Dz * s_Dz) <= s_R2 then
						return true
					end
				end
			end
		end
	end

	return false
end

-- =============================================
-- Grid helpers
-- =============================================

function ClientNavmeshBaker:_CellSize()
	-- A bake or a loaded mesh snapshots the cell size it uses, so all grid math stays
	-- consistent with the cells in memory even if the Config slider is changed afterwards.
	if self.m_ActiveCellSize ~= nil and self.m_ActiveCellSize > 0 then
		return self.m_ActiveCellSize
	end
	-- Config is authoritative (set from the F12 UI); fall back to the registry default.
	local s_Size = Config.NavmeshCellSize
	if s_Size == nil or s_Size <= 0 then
		s_Size = Registry.NAVMESH.CELL_SIZE
	end
	return s_Size
end

-- Overlay draw range (meters). Config is authoritative (live-tunable); falls back to registry.
function ClientNavmeshBaker:_DrawRange()
	local s_Range = Config.NavmeshDrawRange
	if s_Range == nil or s_Range <= 0 then
		s_Range = Registry.NAVMESH.DRAW_RANGE
	end
	return s_Range
end

-- Cells probed per bake step. Config is authoritative (live-tunable from the F12 UI);
-- falls back to the registry default.
function ClientNavmeshBaker:_CellsPerTick()
	local s_Count = Config.NavmeshCellsPerTick
	if s_Count == nil or s_Count < 1 then
		s_Count = Registry.NAVMESH.CELLS_PER_TICK
	end
	return s_Count
end

-- Seconds between bake steps. Config is authoritative (live-tunable); falls back to
-- the registry default. 0 means step every frame.
function ClientNavmeshBaker:_StepInterval()
	local s_Interval = Config.NavmeshStepInterval
	if s_Interval == nil or s_Interval < 0 then
		s_Interval = Registry.NAVMESH.STEP_INTERVAL
	end
	return s_Interval
end

function ClientNavmeshBaker:_WorldToGrid(p_X, p_Z)
	local s_Size = self:_CellSize()
	return math.floor(p_X / s_Size), math.floor(p_Z / s_Size)
end

function ClientNavmeshBaker:_GridToWorldCenter(p_Gx, p_Gz)
	local s_Size = self:_CellSize()
	return (p_Gx + 0.5) * s_Size, (p_Gz + 0.5) * s_Size
end

function ClientNavmeshBaker:_VerticalIndex(p_Y)
	return math.floor(p_Y / Registry.NAVMESH.VERTICAL_RESOLUTION)
end

function ClientNavmeshBaker:_CellKey(p_Gx, p_Gz, p_Gy)
	return p_Gx .. ':' .. p_Gz .. ':' .. p_Gy
end

-- Enqueue a candidate cell unless an equivalent (gx,gz,gy) has already been visited.
-- p_FromY is the floor height of the cell we expanded from (nil for seeds); it is
-- used to enforce the max-step connectivity limit when the candidate is probed.
---@param p_Gx integer
---@param p_Gz integer
---@param p_ExpectedY number
---@param p_FromY number|nil
---@return boolean @true if newly enqueued
function ClientNavmeshBaker:_EnqueueCell(p_Gx, p_Gz, p_ExpectedY, p_FromY)
	local s_Gy = self:_VerticalIndex(p_ExpectedY)
	local s_Key = self:_CellKey(p_Gx, p_Gz, s_Gy)

	if self.m_Visited[s_Key] then
		return false
	end

	-- Keep the flood-fill inside the play area. Mark out-of-bound cells visited so the
	-- (relatively costly) bound test is not repeated for them from other neighbours.
	if not self:_IsWithinBound(p_Gx, p_Gz) then
		self.m_Visited[s_Key] = true
		return false
	end

	self.m_Frontier[#self.m_Frontier + 1] = { gx = p_Gx, gz = p_Gz, expectedY = p_ExpectedY, fromY = p_FromY }
	return true
end

-- =============================================
-- Probing
-- =============================================

-- Probe a single candidate cell. Returns floorY if walkable, or nil if blocked.
---@param p_Gx integer
---@param p_Gz integer
---@param p_ExpectedY number
---@return number|nil
function ClientNavmeshBaker:_ProbeCell(p_Gx, p_Gz, p_ExpectedY)
	local s_Wx, s_Wz = self:_GridToWorldCenter(p_Gx, p_Gz)

	-- 1) Downward ray to find the floor.
	local s_Start = Vec3(s_Wx, p_ExpectedY + Registry.NAVMESH.PROBE_UP, s_Wz)
	local s_End = Vec3(s_Wx, p_ExpectedY - Registry.NAVMESH.PROBE_DOWN, s_Wz)

	---@type RayCastFlags
	local s_Flags = RayCastFlags.DontCheckWater | RayCastFlags.DontCheckCharacter | RayCastFlags.DontCheckRagdoll |
		RayCastFlags.CheckDetailMesh

	local s_FloorHit = RaycastManager:Raycast(s_Start, s_End, s_Flags)
	if s_FloorHit == nil or s_FloorHit.position == nil then
		return nil
	end

	local s_FloorY = s_FloorHit.position.y

	-- 2) Slope check via the surface normal (guarded: not all hits expose a usable normal).
	if s_FloorHit.normal ~= nil then
		local s_MinUp = self:_MinNormalUp()
		if s_FloorHit.normal.y < s_MinUp then
			return nil
		end
	end

	-- 3) Standing-clearance check: nothing low overhead.
	local s_ClearStart = Vec3(s_Wx, s_FloorY + 0.15, s_Wz)
	local s_ClearEnd = Vec3(s_Wx, s_FloorY + Registry.NAVMESH.CLEARANCE, s_Wz)
	local s_ClearHit = RaycastManager:Raycast(s_ClearStart, s_ClearEnd, s_Flags)
	if s_ClearHit ~= nil and s_ClearHit.position ~= nil then
		return nil
	end

	return s_FloorY
end

-- Convert the configured max-slope (degrees, from the F12 UI) into a min normal-up value.
function ClientNavmeshBaker:_MinNormalUp()
	local s_Degrees = Config.NavmeshMaxSlope
	if s_Degrees == nil or s_Degrees <= 0 then
		return Registry.NAVMESH.MIN_NORMAL_UP
	end
	return math.cos(math.rad(s_Degrees))
end

-- =============================================
-- Update loop
-- =============================================

---VEXT Shared UpdateManager:Update Event
---@param p_DeltaTime number
---@param p_UpdatePass UpdatePass|integer
function ClientNavmeshBaker:OnUpdateManagerUpdate(p_DeltaTime, p_UpdatePass)
	-- Match the node editor: do the heavy work in the pre-sim pass only.
	if p_UpdatePass ~= UpdatePass.UpdatePass_PreSim then
		return
	end

	self:_SyncArmedState()

	-- A save in progress must always run to completion, even if the baker was just
	-- disabled, so the database is left in a consistent state. Throttle it in time so
	-- the network buffer is never flooded.
	if self.m_Saving then
		self.m_SaveTimer = self.m_SaveTimer + p_DeltaTime
		if self.m_SaveTimer >= Registry.NAVMESH.SAVE_STEP_INTERVAL then
			self.m_SaveTimer = 0.0
			self:_StepSave()
		end
		return
	end

	-- Keep the overlay buffers fresh (throttled internally; never runs in the draw call).
	-- Runs regardless of armed state so a baked navmesh can be viewed alongside the
	-- waypoint overlay even after the baker is turned off.
	self:_UpdateDrawBuffers(p_DeltaTime)

	-- Editor brush raycast + apply (raycasts only resolve in this pre-sim pass).
	self:_UpdateEditor(p_DeltaTime)

	if not self.m_Armed then
		return
	end

	-- Request the trace waypoints once, to use them as seeds.
	if not self.m_RequestDataSent then
		NetEvents:SendLocal('NodeEditor:RequestData')
		self.m_RequestDataSent = true
	end

	-- Auto-start the bake once the waypoints have arrived. The server sends them in a
	-- single message that can take a while on a large map, so we wait for them and
	-- re-request if needed. Only after a long wait with no waypoints at all do we fall
	-- back to the player's position (which would otherwise bake just the spawn area).
	if self.m_AutoStartPending and self.m_State == BakeState.Idle then
		self.m_AutoStartTimer = self.m_AutoStartTimer + p_DeltaTime
		local s_HaveSeeds = #self.m_SeedWaypoints > 0

		if not s_HaveSeeds then
			self.m_SeedRequestTimer = self.m_SeedRequestTimer + p_DeltaTime
			if self.m_SeedRequestTimer >= 3.0 then
				self.m_SeedRequestTimer = 0.0
				NetEvents:SendLocal('NodeEditor:RequestData')
			end
		end

		if (s_HaveSeeds and self.m_AutoStartTimer >= 1.0) or self.m_AutoStartTimer >= 20.0 then
			-- Only clear the pending flag once the bake actually starts; otherwise keep
			-- retrying (e.g. armed while dead, before a soldier/seeds are available).
			if self:StartBake() then
				self.m_AutoStartPending = false
			else
				self.m_AutoStartTimer = 0.0
			end
		end
	end

	if self.m_State ~= BakeState.Running then
		return
	end

	-- Throttle bake-steps so the raycast load is decoupled from the frame rate.
	self.m_TickTimer = self.m_TickTimer + p_DeltaTime
	if self.m_TickTimer < self:_StepInterval() then
		return
	end
	self.m_TickTimer = 0.0

	self:_StepBake()
end

-- Process up to _CellsPerTick() frontier cells this step.
function ClientNavmeshBaker:_StepBake()
	local s_Budget = self:_CellsPerTick()
	local s_Processed = 0

	while s_Processed < s_Budget do
		-- Frontier exhausted -> bake complete.
		if self.m_FrontierHead > #self.m_Frontier then
			self.m_State = BakeState.Done
			m_Logger:Write('Navmesh bake complete: ' .. tostring(self.m_WalkableCount) .. ' walkable cells.')
			self:_AutoSaveIfNeeded()
			return
		end

		-- Safety cap.
		if self.m_WalkableCount >= Registry.NAVMESH.MAX_CELLS then
			self.m_State = BakeState.Done
			m_Logger:Warning('Navmesh bake hit the MAX_CELLS cap (' ..
				tostring(Registry.NAVMESH.MAX_CELLS) .. '). Stopping.')
			self:_AutoSaveIfNeeded()
			return
		end

		local s_Candidate = self.m_Frontier[self.m_FrontierHead]
		self.m_FrontierHead = self.m_FrontierHead + 1
		s_Processed = s_Processed + 1

		local s_Gy = self:_VerticalIndex(s_Candidate.expectedY)
		local s_Key = self:_CellKey(s_Candidate.gx, s_Candidate.gz, s_Gy)

		-- Could have been visited after it was enqueued.
		if not self.m_Visited[s_Key] then
			self.m_Visited[s_Key] = true

			local s_FloorY = self:_ProbeCell(s_Candidate.gx, s_Candidate.gz, s_Candidate.expectedY)

			-- Enforce the max-step connectivity limit: a cell whose floor is too far
			-- above/below the cell we came from is a cliff/ledge, not a walkable step.
			if s_FloorY ~= nil and s_Candidate.fromY ~= nil then
				if math.abs(s_FloorY - s_Candidate.fromY) > Registry.NAVMESH.MAX_STEP then
					s_FloorY = nil
				end
			end

			if s_FloorY ~= nil then
				-- Re-key on the *actual* floor height so the visited/cell maps line up.
				local s_RealGy = self:_VerticalIndex(s_FloorY)
				local s_RealKey = self:_CellKey(s_Candidate.gx, s_Candidate.gz, s_RealGy)
				self.m_Visited[s_RealKey] = true

				if self.m_Cells[s_RealKey] == nil then
					local s_Wx, s_Wz = self:_GridToWorldCenter(s_Candidate.gx, s_Candidate.gz)
					self.m_Cells[s_RealKey] = {
						x = s_Wx,
						y = s_FloorY,
						z = s_Wz,
						gx = s_Candidate.gx,
						gz = s_Candidate.gz,
						gy = s_RealGy,
					}
					self.m_WalkableCount = self.m_WalkableCount + 1

					-- Expand to the 4-neighbourhood. Each neighbour inherits this cell's
					-- floor as its parent height for the step check when it is probed.
					self:_TryExpand(s_Candidate.gx + 1, s_Candidate.gz, s_FloorY)
					self:_TryExpand(s_Candidate.gx - 1, s_Candidate.gz, s_FloorY)
					self:_TryExpand(s_Candidate.gx, s_Candidate.gz + 1, s_FloorY)
					self:_TryExpand(s_Candidate.gx, s_Candidate.gz - 1, s_FloorY)
				end
			else
				self.m_BlockedCount = self.m_BlockedCount + 1
			end
		end
	end

	-- Compact the frontier: it is an ever-growing array with a moving head, so without
	-- this the already-processed entries (millions, on a large bake) are never freed and
	-- the client eventually runs out of memory. Periodically drop the consumed prefix.
	if self.m_FrontierHead > 50000 then
		local s_Remaining = {}
		for l_Index = self.m_FrontierHead, #self.m_Frontier do
			s_Remaining[#s_Remaining + 1] = self.m_Frontier[l_Index]
		end
		self.m_Frontier = s_Remaining
		self.m_FrontierHead = 1
	end
end

-- Enqueue a neighbour. Its expected floor is the parent's floor; when it is probed,
-- the resulting floor is re-checked against MAX_STEP relative to fromY so we don't
-- connect across cliffs/ledges.
function ClientNavmeshBaker:_TryExpand(p_Gx, p_Gz, p_FromFloorY)
	self:_EnqueueCell(p_Gx, p_Gz, p_FromFloorY, p_FromFloorY)
end

-- =============================================
-- Persistence
-- =============================================

-- Persist automatically once a bake finishes, so the toggle-only workflow needs no
-- console command. Runs at most once per bake.
function ClientNavmeshBaker:_AutoSaveIfNeeded()
	if self.m_AutoSaved then
		return
	end
	self.m_AutoSaved = true
	self:SaveBake()
end

-- Begin a streaming save. The actual batches are sent a few per frame from
-- _StepSave so the network buffer is never flooded (which would kick the client).
function ClientNavmeshBaker:SaveBake()
	if self.m_WalkableCount == 0 then
		m_Logger:Write('Nothing to save: enable the Navmesh Baker to bake first.')
		return
	end

	if self.m_Saving then
		m_Logger:Write('Navmesh save already in progress.')
		return
	end

	-- Flatten the cell map into an array we can stream over multiple frames.
	self.m_SaveQueue = {}
	for _, l_Cell in pairs(self.m_Cells) do
		self.m_SaveQueue[#self.m_SaveQueue + 1] = l_Cell
	end
	self.m_SaveCursor = 1
	self.m_Saving = true

	NetEvents:SendLocal('Navmesh:StoreBegin', { cellSize = self:_CellSize(), total = #self.m_SaveQueue })
	m_Logger:Write('Saving ' .. tostring(#self.m_SaveQueue) .. ' navmesh cells (streaming)...')
end

-- Send a few batches per frame until the queue is drained, then commit.
function ClientNavmeshBaker:_StepSave()
	local s_BatchSize = Registry.NAVMESH.STORE_BATCH_SIZE
	local s_BatchesThisTick = 0

	while s_BatchesThisTick < Registry.NAVMESH.SAVE_BATCHES_PER_TICK do
		-- Queue drained -> commit and finish.
		if self.m_SaveCursor > #self.m_SaveQueue then
			NetEvents:SendLocal('Navmesh:StoreCommit')
			self.m_Saving = false
			self.m_SaveQueue = {}
			m_Logger:Write('Navmesh save streamed to server.')
			return
		end

		local s_Batch = {}
		for _ = 1, s_BatchSize do
			local l_Cell = self.m_SaveQueue[self.m_SaveCursor]
			if l_Cell == nil then
				break
			end
			s_Batch[#s_Batch + 1] = {
				gx = l_Cell.gx,
				gz = l_Cell.gz,
				gy = l_Cell.gy,
				x = l_Cell.x,
				y = l_Cell.y,
				z = l_Cell.z,
			}
			self.m_SaveCursor = self.m_SaveCursor + 1
		end

		NetEvents:SendLocal('Navmesh:StoreBatch', s_Batch)
		s_BatchesThisTick = s_BatchesThisTick + 1
	end
end

-- =============================================
-- NetEvents
-- =============================================

-- Re-use the node editor's data feed for seeds.
---@param p_WayPoints table
function ClientNavmeshBaker:OnReceiveNodes(p_WayPoints)
	if not self.m_Armed then
		return
	end

	for l_Index = 1, #p_WayPoints do
		self.m_SeedWaypoints[#self.m_SeedWaypoints + 1] = p_WayPoints[l_Index]
	end
end

-- =============================================
-- Drawing
-- =============================================

---VEXT Client UI:DrawHud Event
-- Renders the pre-built overlay buffers only - no computation happens here.
function ClientNavmeshBaker:OnUIDrawHud()
	-- The baker status line only shows while the baker is actually active.
	if self.m_Armed or self.m_Saving then
		self:_DrawStatusText()
	end

	-- Editor HUD + brush cursor (independent of the overlay toggle).
	if self.m_EditorActive then
		self:_DrawEditorHud()
		if self.m_EditMode then
			self:_DrawBrushCursor()
		end
	end

	-- The overlay renders whenever it is enabled and there is something baked this
	-- session, independent of the baker being armed - so it can sit alongside the
	-- waypoint overlay (enable both "Draw Navmesh" and "Debug Trace Paths").
	if not Config.DrawNavmesh then
		return
	end

	-- Grid lines first, then the cell points on top.
	for l_Index = 1, #self.m_DrawLines do
		local l_Line = self.m_DrawLines[l_Index]
		DebugRenderer:DrawLine(l_Line.from, l_Line.to, l_Line.color, l_Line.color)
	end

	-- Small fixed size like the node editor's waypoint dots (the grid lines carry the look).
	local s_NodeSize = Registry.NAVMESH.NODE_SIZE
	for l_Index = 1, #self.m_DrawNodes do
		local l_Node = self.m_DrawNodes[l_Index]
		-- Last arg = smallSizeSegmentDecrease: far nodes draw cheaper (quality scaling).
		DebugRenderer:DrawSphere(l_Node.pos, s_NodeSize, l_Node.color, false, l_Node.low)
	end
end

-- Find the walkable cell at (gx,gz) closest in height to p_Gy, checking the level and the
-- two vertical neighbours so grid lines connect across small slope steps.
---@return table|nil
function ClientNavmeshBaker:_FindNeighbour(p_Gx, p_Gz, p_Gy)
	local s_Cell = self.m_Cells[self:_CellKey(p_Gx, p_Gz, p_Gy)]
	if s_Cell then return s_Cell end
	s_Cell = self.m_Cells[self:_CellKey(p_Gx, p_Gz, p_Gy + 1)]
	if s_Cell then return s_Cell end
	return self.m_Cells[self:_CellKey(p_Gx, p_Gz, p_Gy - 1)]
end

-- Rebuild the overlay buffers from the cells in a window around the player. Throttled,
-- and only when the player crosses into a new cell, so this never runs every frame and
-- never in the draw callback. Produces points + grid lines (the "mesh" look) and tints
-- by height, then atomically swaps the result into the live buffers.
---@param p_DeltaTime number
function ClientNavmeshBaker:_UpdateDrawBuffers(p_DeltaTime)
	if not Config.DrawNavmesh or self.m_WalkableCount == 0 then
		return
	end

	local s_Player = PlayerManager:GetLocalPlayer()
	if s_Player == nil or s_Player.soldier == nil or s_Player.soldier.worldTransform == nil then
		return
	end

	local s_PlayerPos = s_Player.soldier.worldTransform.trans
	local s_CellSize = self:_CellSize()
	local s_Pgx = math.floor(s_PlayerPos.x / s_CellSize)
	local s_Pgz = math.floor(s_PlayerPos.z / s_CellSize)
	local s_Pgy = math.floor(s_PlayerPos.y / Registry.NAVMESH.VERTICAL_RESOLUTION)
	local s_Key = self:_CellKey(s_Pgx, s_Pgz, s_Pgy)

	-- Rebuild on cell change, or on a slow timer so a growing bake's new cells still show.
	self.m_DrawRebuildTimer = self.m_DrawRebuildTimer + p_DeltaTime
	if s_Key == self.m_LastDrawCellKey and self.m_DrawRebuildTimer < Registry.NAVMESH.DRAW_REBUILD_INTERVAL then
		return
	end
	self.m_LastDrawCellKey = s_Key
	self.m_DrawRebuildTimer = 0.0

	local s_Nodes = {}
	local s_Lines = {}

	local s_Range = self:_DrawRange()
	-- Cap the window in cells too, so a small cell size cannot blow up the lookup count.
	local s_Radius = math.min(math.ceil(s_Range / s_CellSize), 60)
	local s_RangeSq = s_Range * s_Range
	local s_FarSq = s_RangeSq * 0.25
	local s_MaxCells = Registry.NAVMESH.DRAW_MAX_SPHERES
	local s_LineColor = Vec4(0.0, 0.7, 0.32, 0.5)
	local s_Count = 0

	for l_Dx = -s_Radius, s_Radius do
		for l_Dz = -s_Radius, s_Radius do
			-- Player's vertical level plus one above/below for stacked surfaces.
			for l_Dy = -1, 1 do
				local s_Cell = self.m_Cells[self:_CellKey(s_Pgx + l_Dx, s_Pgz + l_Dz, s_Pgy + l_Dy)]
				if s_Cell ~= nil then
					local s_Ddx = s_Cell.x - s_PlayerPos.x
					local s_Ddz = s_Cell.z - s_PlayerPos.z
					local s_Dist2 = s_Ddx * s_Ddx + s_Ddz * s_Ddz

					if s_Dist2 <= s_RangeSq then
						local s_Pos = Vec3(s_Cell.x, s_Cell.y, s_Cell.z)
						s_Nodes[#s_Nodes + 1] = {
							pos = s_Pos,
							color = self:_HeightColor(s_Cell.y - s_PlayerPos.y),
							low = s_Dist2 > s_FarSq, -- cheaper spheres past half range
						}

						-- Grid lines to the +X and +Z neighbours (one direction each to
						-- avoid drawing every edge twice).
						local s_NX = self:_FindNeighbour(s_Cell.gx + 1, s_Cell.gz, s_Cell.gy)
						if s_NX then
							s_Lines[#s_Lines + 1] = { from = s_Pos, to = Vec3(s_NX.x, s_NX.y, s_NX.z), color = s_LineColor }
						end
						local s_NZ = self:_FindNeighbour(s_Cell.gx, s_Cell.gz + 1, s_Cell.gy)
						if s_NZ then
							s_Lines[#s_Lines + 1] = { from = s_Pos, to = Vec3(s_NZ.x, s_NZ.y, s_NZ.z), color = s_LineColor }
						end

						s_Count = s_Count + 1
						if s_Count >= s_MaxCells then
							goto done
						end
					end
				end
			end
		end
	end
	::done::

	-- Atomic swap.
	self.m_DrawNodes = s_Nodes
	self.m_DrawLines = s_Lines
end

-- Tint a cell by its height relative to the player: green at the player's level, shifting
-- toward yellow above and blue below, so elevation reads at a glance.
---@param p_DeltaY number
---@return Vec4
function ClientNavmeshBaker:_HeightColor(p_DeltaY)
	local s_T = math.max(-1.0, math.min(1.0, p_DeltaY / 8.0))
	if s_T >= 0 then
		-- player level (green) -> above (yellow)
		return Vec4(0.1 + 0.8 * s_T, 1.0, 0.45 - 0.35 * s_T, 0.55)
	else
		-- player level (green) -> below (blue)
		return Vec4(0.1, 1.0 + 0.5 * s_T, 0.45 - 0.45 * s_T, 0.55)
	end
end

-- Draw a 2D status line for the baker (top-left of the screen).
function ClientNavmeshBaker:_DrawStatusText()
	local s_Status
	local s_Color = Vec4(1.0, 1.0, 1.0, 1.0)

	if self.m_Saving then
		local s_Pct = 0
		if #self.m_SaveQueue > 0 then
			s_Pct = math.floor((self.m_SaveCursor - 1) / #self.m_SaveQueue * 100)
		end
		s_Status = 'saving... ' .. tostring(s_Pct) .. '%'
		s_Color = Vec4(1.0, 0.6, 0.1, 1.0)
	elseif self.m_State == BakeState.Running then
		s_Status = 'baking... ' .. tostring(self.m_WalkableCount) .. ' cells (' ..
			tostring(#self.m_Frontier - self.m_FrontierHead + 1) .. ' queued)'
		s_Color = Vec4(1.0, 0.85, 0.2, 1.0)
	elseif self.m_State == BakeState.Done then
		s_Status = 'done - ' .. tostring(self.m_WalkableCount) .. ' cells' ..
			(self.m_AutoSaved and ' (saved to mod.db)' or '')
		if not self.m_SeededFromWaypoints then
			s_Status = s_Status .. ' [spawn area only - no waypoints received]'
		end
		s_Color = Vec4(0.2, 1.0, 0.4, 1.0)
	elseif self.m_AutoStartPending then
		s_Status = 'starting...'
		s_Color = Vec4(0.6, 0.8, 1.0, 1.0)
	else
		s_Status = 'idle'
	end

	DebugRenderer:DrawText2D(30.0, 200.0, 'Navmesh Baker: ' .. s_Status, s_Color, 1.2)
end

-- =============================================
-- Editor
-- =============================================

-- Mirror Config.NavmeshEditor. Entering loads the saved navmesh if memory is empty.
function ClientNavmeshBaker:_SyncEditorState()
	local s_Should = Config.NavmeshEditor == true
	if s_Should == self.m_EditorActive then
		return
	end
	self.m_EditorActive = s_Should

	if s_Should then
		m_Logger:Write('Navmesh editor enabled. Press ALT to toggle brush editing.')
		self.m_EditMode = false
		self.m_BoxCornerA = nil
		-- Pull the saved mesh from the server if we have nothing in memory yet.
		if self.m_WalkableCount == 0 and not self.m_Loading then
			self:RequestClientLoad()
		end
	else
		self.m_EditMode = false
		self:_EndStroke()
		self.m_BoxCornerA = nil
		m_Logger:Write('Navmesh editor disabled.')
	end
end

-- Ask the server to stream the saved navmesh back to us for editing.
function ClientNavmeshBaker:RequestClientLoad()
	self.m_Loading = true
	NetEvents:SendLocal('Navmesh:RequestLoad')
	m_Logger:Write('Requesting navmesh from server...')
end

---@param p_Info table @{ cellSize, total }
function ClientNavmeshBaker:OnLoadBegin(p_Info)
	self:ResetBake()
	self.m_Loading = true
	self.m_UndoStack = {}
	self.m_UnsavedEdits = 0
	if p_Info and p_Info.cellSize and p_Info.cellSize > 0 then
		self.m_ActiveCellSize = p_Info.cellSize
	end
end

---@param p_Batch table[]
function ClientNavmeshBaker:OnLoadBatch(p_Batch)
	if not self.m_Loading then
		return
	end
	for l_Index = 1, #p_Batch do
		local l_Cell = p_Batch[l_Index]
		-- Coerce grid coords to integers: they come back from SQL as floats (17.0), which
		-- would make string keys like "17.0:26.0:66.0" that never match the integer keys
		-- the overlay/brush compute via math.floor ("17:26:66").
		local s_Gx = math.floor(l_Cell.gx + 0.5)
		local s_Gz = math.floor(l_Cell.gz + 0.5)
		local s_Gy = math.floor(l_Cell.gy + 0.5)
		local s_Key = self:_CellKey(s_Gx, s_Gz, s_Gy)
		if self.m_Cells[s_Key] == nil then
			self.m_Cells[s_Key] = { x = l_Cell.x, y = l_Cell.y, z = l_Cell.z, gx = s_Gx, gz = s_Gz, gy = s_Gy }
			self.m_WalkableCount = self.m_WalkableCount + 1
		end
	end
end

function ClientNavmeshBaker:OnLoadCommit()
	self.m_Loading = false

	-- Derive the exact cell size from the loaded data so the overlay/editing grid lines
	-- up with the cells, regardless of what the meta reported. The baker stores each cell
	-- at world x = (gx + 0.5) * cellSize, so cellSize = x / (gx + 0.5).
	for _, l_Cell in pairs(self.m_Cells) do
		local s_Denom = l_Cell.gx + 0.5
		if s_Denom ~= 0 then
			local s_Derived = math.floor((l_Cell.x / s_Denom) * 1000 + 0.5) / 1000
			if s_Derived > 0 then
				self.m_ActiveCellSize = s_Derived
			end
		end
		break
	end

	self.m_LastDrawCellKey = nil -- force overlay rebuild
	m_Logger:Write('Navmesh loaded for editing: ' .. tostring(self.m_WalkableCount) ..
		' cells (cell size ' .. tostring(self.m_ActiveCellSize) .. ').')
end

-- Camera-forward raycast (same approach as the node editor) for the brush cursor.
---@param p_MaxDistance number
---@return RayCastHit|nil
function ClientNavmeshBaker:_CameraRaycast(p_MaxDistance)
	local s_Transform = ClientUtils:GetCameraTransform()
	if s_Transform == nil or s_Transform.trans == Vec3.zero then
		return nil
	end
	local s_Dir = Vec3(-s_Transform.forward.x, -s_Transform.forward.y, -s_Transform.forward.z)
	local s_Start = s_Transform.trans
	local s_End = Vec3(s_Start.x + s_Dir.x * p_MaxDistance, s_Start.y + s_Dir.y * p_MaxDistance, s_Start.z + s_Dir.z * p_MaxDistance)
	---@type RayCastFlags
	local s_Flags = RayCastFlags.DontCheckWater | RayCastFlags.DontCheckCharacter | RayCastFlags.DontCheckRagdoll | RayCastFlags.CheckDetailMesh
	return RaycastManager:Raycast(s_Start, s_End, s_Flags)
end

---VEXT Client Client:UpdateInput Event
---@param p_DeltaTime number
function ClientNavmeshBaker:OnClientUpdateInput(p_DeltaTime)
	self:_SyncEditorState()
	if not self.m_EditorActive then
		return
	end

	-- Pressing F12 opens a menu - always drop edit mode so the editor never fights it.
	if InputManager:WentKeyDown(InputDeviceKeys.IDK_F12) then
		self.m_EditMode = false
		self:_EndStroke()
	end

	-- While the WebUI holds the cursor (F12 menu open), do not touch input - so the
	-- menu stays fully usable and LMB clicks go to it, not the brush.
	if self.m_UiCapturing then
		return
	end

	-- ALT toggles brush-edit interaction.
	if InputManager:WentKeyDown(InputDeviceKeys.IDK_LeftAlt) then
		self.m_EditMode = not self.m_EditMode
		self:_EndStroke()
		self.m_BoxCornerA = nil
	end

	-- Tool / brush / overlay toggles.
	if InputManager:WentKeyDown(InputDeviceKeys.IDK_1) then self.m_Tool = 'paint' end
	if InputManager:WentKeyDown(InputDeviceKeys.IDK_2) then self.m_Tool = 'erase' end
	if InputManager:WentKeyDown(InputDeviceKeys.IDK_3) then
		self.m_Tool = 'box'
		self.m_BoxCornerA = nil
	end
	if InputManager:WentKeyDown(InputDeviceKeys.IDK_Subtract) then self:_AdjustBrush(-Registry.NAVMESH.BRUSH_STEP) end
	if InputManager:WentKeyDown(InputDeviceKeys.IDK_Add) then self:_AdjustBrush(Registry.NAVMESH.BRUSH_STEP) end
	if InputManager:WentKeyDown(InputDeviceKeys.IDK_N) then Config.DrawNavmesh = not Config.DrawNavmesh end
	if InputManager:WentKeyDown(InputDeviceKeys.IDK_B) then self:_ToggleWaypoints() end
	if InputManager:IsKeyDown(InputDeviceKeys.IDK_LeftControl) and InputManager:WentKeyDown(InputDeviceKeys.IDK_Z) then
		self:_Undo()
	end
	-- Save/load/exit on likely-free letters (H/U/O). If these do not register on your
	-- setup, the live key-test below tells you which candidate keys do work.
	if InputManager:WentKeyDown(InputDeviceKeys.IDK_H) then self:SaveBake() end
	if InputManager:WentKeyDown(InputDeviceKeys.IDK_U) then self:RequestClientLoad() end
	if InputManager:WentKeyDown(InputDeviceKeys.IDK_O) then
		Config.NavmeshEditor = false
		NetEvents:SendLocal('ConsoleCommands:SetConfig', 'NavmeshEditor', 'false')
	end

	-- DIAGNOSTIC: live held-state of candidate keys so we can find ones that register
	-- on this machine. Hold each and watch the "key test" line in the HUD.
	self.m_DbgKeys = {
		H = InputManager:IsKeyDown(InputDeviceKeys.IDK_H),
		U = InputManager:IsKeyDown(InputDeviceKeys.IDK_U),
		O = InputManager:IsKeyDown(InputDeviceKeys.IDK_O),
		J = InputManager:IsKeyDown(InputDeviceKeys.IDK_J),
		K = InputManager:IsKeyDown(InputDeviceKeys.IDK_K),
		L = InputManager:IsKeyDown(InputDeviceKeys.IDK_L),
		M = InputManager:IsKeyDown(InputDeviceKeys.IDK_M),
	}
	-- Note: the brush raycast + LMB apply are handled in _UpdateEditor (pre-sim pass).
	-- Raycasts do not resolve from the Client:UpdateInput event.
end

-- Brush raycast + LMB application. Runs in the pre-sim pass (the only place client
-- raycasts resolve - the node editor does the same).
---@param p_DeltaTime number
function ClientNavmeshBaker:_UpdateEditor(p_DeltaTime)
	if not self.m_EditorActive or self.m_UiCapturing or not self.m_EditMode then
		self.m_BrushHit = nil
		self.m_FireWasDown = false
		return
	end

	-- Raycast for the brush cursor.
	self.m_BrushHit = nil
	local s_Hit = self:_CameraRaycast(120.0)
	if s_Hit ~= nil and s_Hit.position ~= nil then
		self.m_BrushHit = s_Hit.position
	end

	-- LMB (level captured in the input hook) drives the brush.
	local s_FireDown = self.m_FireLevel > 0
	local s_WentDown = s_FireDown and not self.m_FireWasDown
	local s_WentUp = (not s_FireDown) and self.m_FireWasDown
	self.m_FireWasDown = s_FireDown

	if self.m_Tool == 'box' then
		if s_WentDown then self:_BoxClick() end
	else
		if s_WentDown then self:_BeginStroke() end
		if s_FireDown and self.m_BrushHit ~= nil and self.m_CurrentStroke ~= nil then
			self.m_BrushTimer = self.m_BrushTimer + p_DeltaTime
			if self.m_BrushTimer >= 0.04 then
				self.m_BrushTimer = 0.0
				self:_ApplyBrush()
			end
		end
		if s_WentUp then self:_EndStroke() end
	end
end

---VEXT Client Input:PreUpdate Hook
function ClientNavmeshBaker:OnInputPreUpdate(p_HookCtx, p_Cache, p_DeltaTime)
	-- Capture LMB before any suppression so the editor can still read it.
	self.m_FireLevel = p_Cache:GetLevel(InputConceptIdentifiers.ConceptFire)
	-- While brush editing (and not in a menu), stop the weapon from actually firing.
	if self.m_EditorActive and self.m_EditMode and not self.m_UiCapturing then
		p_Cache:SetLevel(InputConceptIdentifiers.ConceptFire, 0.0)
	end
end

-- Called by the WebUI layer (UIViews) when it grabs or releases the cursor, so the
-- editor knows to step out of the way of the menu.
---@param p_Value boolean
function ClientNavmeshBaker:SetUiCapturing(p_Value)
	self.m_UiCapturing = p_Value
	if p_Value then
		self.m_EditMode = false
		self:_EndStroke()
		self.m_BoxCornerA = nil
	end
end

function ClientNavmeshBaker:_AdjustBrush(p_Delta)
	self.m_BrushRadius = math.max(Registry.NAVMESH.BRUSH_MIN,
		math.min(Registry.NAVMESH.BRUSH_MAX, self.m_BrushRadius + p_Delta))
end

function ClientNavmeshBaker:_ToggleWaypoints()
	Config.DebugTracePaths = not Config.DebugTracePaths
	if m_ClientNodeEditor ~= nil and m_ClientNodeEditor.OnSetEnabled ~= nil then
		m_ClientNodeEditor:OnSetEnabled(Config.DebugTracePaths)
	end
end

function ClientNavmeshBaker:_BeginStroke()
	self.m_CurrentStroke = { added = {}, removed = {} }
	self.m_BrushTimer = 1.0 -- apply on the first frame
end

function ClientNavmeshBaker:_EndStroke()
	if self.m_CurrentStroke == nil then
		return
	end
	local s_Stroke = self.m_CurrentStroke
	self.m_CurrentStroke = nil

	local s_Count = #s_Stroke.added
	for _ in pairs(s_Stroke.removed) do s_Count = s_Count + 1 end
	if s_Count == 0 then
		return
	end

	self.m_UndoStack[#self.m_UndoStack + 1] = s_Stroke
	while #self.m_UndoStack > Registry.NAVMESH.UNDO_LIMIT do
		table.remove(self.m_UndoStack, 1)
	end
	self.m_UnsavedEdits = self.m_UnsavedEdits + s_Count
end

function ClientNavmeshBaker:_ApplyBrush()
	if self.m_BrushHit == nil or self.m_CurrentStroke == nil then
		return
	end
	if self.m_Tool == 'paint' then
		self:_PaintAt(self.m_BrushHit, self.m_CurrentStroke)
	elseif self.m_Tool == 'erase' then
		self:_EraseAt(self.m_BrushHit, self.m_CurrentStroke)
	end
	self.m_LastDrawCellKey = nil -- refresh the overlay
end

-- Add walkable cells under the brush, probing each for a floor (reuses the bake probe).
function ClientNavmeshBaker:_PaintAt(p_Hit, p_Stroke)
	local s_CellSize = self:_CellSize()
	local s_R = self.m_BrushRadius
	local s_R2 = s_R * s_R
	local s_RCells = math.ceil(s_R / s_CellSize)
	local s_Cgx, s_Cgz = self:_WorldToGrid(p_Hit.x, p_Hit.z)

	for l_Dx = -s_RCells, s_RCells do
		for l_Dz = -s_RCells, s_RCells do
			local s_Gx, s_Gz = s_Cgx + l_Dx, s_Cgz + l_Dz
			local s_Wx, s_Wz = self:_GridToWorldCenter(s_Gx, s_Gz)
			local s_Ddx, s_Ddz = s_Wx - p_Hit.x, s_Wz - p_Hit.z
			if (s_Ddx * s_Ddx + s_Ddz * s_Ddz) <= s_R2 then
				local s_FloorY = self:_ProbeCell(s_Gx, s_Gz, p_Hit.y)
				if s_FloorY ~= nil and math.abs(s_FloorY - p_Hit.y) <= 2.5 then
					local s_Gy = self:_VerticalIndex(s_FloorY)
					local s_Key = self:_CellKey(s_Gx, s_Gz, s_Gy)
					if self.m_Cells[s_Key] == nil then
						self.m_Cells[s_Key] = { x = s_Wx, y = s_FloorY, z = s_Wz, gx = s_Gx, gz = s_Gz, gy = s_Gy }
						self.m_WalkableCount = self.m_WalkableCount + 1
						p_Stroke.added[#p_Stroke.added + 1] = s_Key
					end
				end
			end
		end
	end
end

-- Remove cells under the brush near the aimed height.
function ClientNavmeshBaker:_EraseAt(p_Hit, p_Stroke)
	local s_CellSize = self:_CellSize()
	local s_R = self.m_BrushRadius
	local s_R2 = s_R * s_R
	local s_RCells = math.ceil(s_R / s_CellSize)
	local s_Cgx, s_Cgz = self:_WorldToGrid(p_Hit.x, p_Hit.z)
	local s_Hgy = self:_VerticalIndex(p_Hit.y)

	for l_Dx = -s_RCells, s_RCells do
		for l_Dz = -s_RCells, s_RCells do
			local s_Gx, s_Gz = s_Cgx + l_Dx, s_Cgz + l_Dz
			local s_Wx, s_Wz = self:_GridToWorldCenter(s_Gx, s_Gz)
			local s_Ddx, s_Ddz = s_Wx - p_Hit.x, s_Wz - p_Hit.z
			if (s_Ddx * s_Ddx + s_Ddz * s_Ddz) <= s_R2 then
				for l_Dy = -1, 1 do
					local s_Key = self:_CellKey(s_Gx, s_Gz, s_Hgy + l_Dy)
					local s_Cell = self.m_Cells[s_Key]
					if s_Cell ~= nil and p_Stroke.removed[s_Key] == nil then
						self.m_Cells[s_Key] = nil
						self.m_WalkableCount = self.m_WalkableCount - 1
						p_Stroke.removed[s_Key] = s_Cell
					end
				end
			end
		end
	end
end

-- Box tool: first click sets a corner, second erases the rectangle between them.
function ClientNavmeshBaker:_BoxClick()
	if self.m_BrushHit == nil then
		return
	end
	if self.m_BoxCornerA == nil then
		self.m_BoxCornerA = self.m_BrushHit:Clone()
		return
	end

	local s_Stroke = { added = {}, removed = {} }
	local s_MinX = math.min(self.m_BoxCornerA.x, self.m_BrushHit.x)
	local s_MaxX = math.max(self.m_BoxCornerA.x, self.m_BrushHit.x)
	local s_MinZ = math.min(self.m_BoxCornerA.z, self.m_BrushHit.z)
	local s_MaxZ = math.max(self.m_BoxCornerA.z, self.m_BrushHit.z)
	-- Constrain to the vertical band of the two corners (+/- margin), so the box only
	-- erases cells near the surface you drew it on - not floors above/below you can't see.
	local s_MinY = math.min(self.m_BoxCornerA.y, self.m_BrushHit.y) - 4.0
	local s_MaxY = math.max(self.m_BoxCornerA.y, self.m_BrushHit.y) + 4.0
	for l_Key, l_Cell in pairs(self.m_Cells) do
		if l_Cell.x >= s_MinX and l_Cell.x <= s_MaxX and l_Cell.z >= s_MinZ and l_Cell.z <= s_MaxZ
			and l_Cell.y >= s_MinY and l_Cell.y <= s_MaxY then
			s_Stroke.removed[l_Key] = l_Cell
		end
	end
	for l_Key, _ in pairs(s_Stroke.removed) do
		self.m_Cells[l_Key] = nil
		self.m_WalkableCount = self.m_WalkableCount - 1
	end

	self.m_CurrentStroke = s_Stroke
	self:_EndStroke()
	self.m_BoxCornerA = nil
	self.m_LastDrawCellKey = nil
end

function ClientNavmeshBaker:_Undo()
	local s_Stroke = table.remove(self.m_UndoStack)
	if s_Stroke == nil then
		return
	end
	for l_I = 1, #s_Stroke.added do
		local s_Key = s_Stroke.added[l_I]
		if self.m_Cells[s_Key] ~= nil then
			self.m_Cells[s_Key] = nil
			self.m_WalkableCount = self.m_WalkableCount - 1
		end
	end
	for l_Key, l_Cell in pairs(s_Stroke.removed) do
		if self.m_Cells[l_Key] == nil then
			self.m_Cells[l_Key] = l_Cell
			self.m_WalkableCount = self.m_WalkableCount + 1
		end
	end
	self.m_LastDrawCellKey = nil
end

-- In-world brush cursor (ring, plus the box rectangle when placing one).
function ClientNavmeshBaker:_DrawBrushCursor()
	local s_Hit = self.m_BrushHit
	if s_Hit == nil then
		return
	end
	local s_Color = Vec4(0.3, 0.8, 1.0, 0.9)
	if self.m_Tool == 'erase' then s_Color = Vec4(1.0, 0.35, 0.3, 0.9) end
	if self.m_Tool == 'box' then s_Color = Vec4(1.0, 0.8, 0.2, 0.9) end

	local s_R = self.m_BrushRadius
	local s_N = 26
	local s_Prev = nil
	for l_I = 0, s_N do
		local s_A = (l_I / s_N) * math.pi * 2
		local s_P = Vec3(s_Hit.x + s_R * math.cos(s_A), s_Hit.y + 0.06, s_Hit.z + s_R * math.sin(s_A))
		if s_Prev ~= nil then
			DebugRenderer:DrawLine(s_Prev, s_P, s_Color, s_Color)
		end
		s_Prev = s_P
	end

	if self.m_Tool == 'box' and self.m_BoxCornerA ~= nil then
		local a, b = self.m_BoxCornerA, s_Hit
		local s_Y = math.max(a.y, b.y) + 0.06
		local p1, p2, p3, p4 = Vec3(a.x, s_Y, a.z), Vec3(b.x, s_Y, a.z), Vec3(b.x, s_Y, b.z), Vec3(a.x, s_Y, b.z)
		DebugRenderer:DrawLine(p1, p2, s_Color, s_Color)
		DebugRenderer:DrawLine(p2, p3, s_Color, s_Color)
		DebugRenderer:DrawLine(p3, p4, s_Color, s_Color)
		DebugRenderer:DrawLine(p4, p1, s_Color, s_Color)
	end
end

-- 2D editor HUD (text rows, like the node editor's labels).
function ClientNavmeshBaker:_DrawEditorHud()
	local s_X = 30.0
	local s_Y = 232.0
	local s_LH = 16.0
	local s_White = Vec4(0.92, 0.97, 0.94, 1.0)
	local s_Muted = Vec4(0.62, 0.73, 0.69, 1.0)
	local s_Accent = Vec4(0.36, 0.91, 0.66, 1.0)

	local function l_Line(p_Text, p_Color)
		DebugRenderer:DrawText2D(s_X, s_Y, p_Text, p_Color or s_White, 1.1)
		s_Y = s_Y + s_LH
	end

	l_Line('NAVMESH EDITOR', s_Accent)
	if self.m_Loading then
		l_Line('loading from server...', s_Muted)
	end
	l_Line(string.format('edit: %s   tool: %s   brush: %.0f m',
		self.m_EditMode and 'ON' or 'off', self.m_Tool, self.m_BrushRadius))
	l_Line(string.format('cells: %d   unsaved edits: %d', self.m_WalkableCount, self.m_UnsavedEdits), s_Muted)
	-- Diagnostics (helps confirm the brush is reading aim + LMB, and the overlay draws).
	l_Line(string.format('aim: %s   LMB: %s   drawn: %d   csize: %.2f',
		self.m_BrushHit and 'hit' or 'none', self.m_FireLevel > 0 and 'DOWN' or 'up',
		#self.m_DrawNodes, self:_CellSize()), s_Muted)
	s_Y = s_Y + 5
	l_Line('ALT edit  |  LMB apply  |  1/2/3 paint/erase/box', s_Muted)
	l_Line('numpad -/+ brush  |  N navmesh  |  B waypoints  |  Ctrl+Z undo', s_Muted)
	l_Line('H SAVE  |  U load from db  |  O EXIT editor', s_Accent)
	-- Live key test: hold a key, see if it shows "1". Tells us which keys register here.
	local s_Dbg = self.m_DbgKeys or {}
	l_Line(string.format('key test (hold): H%d U%d O%d J%d K%d L%d M%d',
		s_Dbg.H and 1 or 0, s_Dbg.U and 1 or 0, s_Dbg.O and 1 or 0,
		s_Dbg.J and 1 or 0, s_Dbg.K and 1 or 0, s_Dbg.L and 1 or 0, s_Dbg.M and 1 or 0), s_Muted)
end

-- =============================================
-- Level lifecycle
-- =============================================

function ClientNavmeshBaker:OnLevelDestroy()
	self:ResetBake()
	self.m_SeedWaypoints = {}
	self.m_RequestDataSent = false
	self.m_ActiveCellSize = nil
	self.m_EditMode = false
	self.m_CurrentStroke = nil
	self.m_BoxCornerA = nil
	self.m_Loading = false
	self.m_UndoStack = {}
	self.m_UnsavedEdits = 0
end

if g_ClientNavmeshBaker == nil then
	---@type ClientNavmeshBaker
	g_ClientNavmeshBaker = ClientNavmeshBaker()
end

return g_ClientNavmeshBaker
