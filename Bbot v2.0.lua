local imgui = require 'mimgui'
local moonloader = require 'lib.moonloader'
local ffi = require 'ffi'
local encoding = require 'encoding'
encoding.default = 'CP1251'
local u8 = encoding.UTF8
local new = imgui.new
local sampev = require 'samp.events'
local vkeys = require 'vkeys'
local dlstatus = require('moonloader').download_status

local CURRENT_VERSION = "2.1"
local VERSION_INFO_URL = 'https://github.com/SaportBati/BBot-v2/raw/refs/heads/main/BbotVersion.ini'
local SCRIPT_DOWNLOAD_URL = 'https://github.com/SaportBati/BBot-v2/raw/refs/heads/main/Bbot%20v2.0.lua'

local UPDATE_DEBUG_MESSAGES = false

local function sendUpdateMessage(text)
	if not UPDATE_DEBUG_MESSAGES then return end
	if type(sampAddChatMessage) ~= 'function' or not text or text == '' then return end
	local prefixed = string.format('{AA77FF}[BBot Update]{FFFFFF} %s', text)
	local encoded = u8:encode(prefixed)
	sampAddChatMessage(u8:decode(encoded, 'CP1251'), -1)
end

-- Central environment table to reduce upvalues in closures
local BB = {}
setmetatable(BB, { __index = _G })
setfenv(1, BB)

isRunning = false
scannerThread = nil
playerLastPos = {}
playerLastTriggeredAt = {}
isProcessing = false
triggeredInRadius = {}
triggeredInRadiusTime = {}
playerInCarPositions = {} -- позиции игроков в машине каждые 10мс
playerInCarLastCheckTime = {} -- время последнего замера позиции для игроков в машине
playerInCarTriggered = {} -- флаг триггера для игроков в машине
teleportDetectionDistance = 50.0 -- расстояние для определения телепорта (в метрах) 
teleportCoords = {}
teleportNames = {}
teleportIndex = 1
lastPlayerFoundAt = 0
prevLeftDown = false
prevRightDown = false
skippedPlayers = {}
lastCommandTime = 0
commandCooldown = 1000
wasSpectating = false
wasKickedFromSpectate = false
reCommandTime = 0 
lastDecisionCloseTime = 0

notifications = {}
notificationMaxCount = 5
notificationDuration = 3.0
notificationFadeIn = 0.3
notificationFadeOut = 0.3

function addNotification(text)
	if not text or text == '' then return end
	local notification = {
		text = text,
		startTime = os.clock(),
		id = os.clock()
	}
	table.insert(notifications, notification)

	if #notifications > notificationMaxCount then
		table.remove(notifications, 1)
	end
end

DecisionOpen = new.bool()
pendingReport = nil
banCountdownStartTime = 0
banCountdownDuration = 4.0
autoBanTriggered = false

WinState = new.bool()
BanLoggerState = new.bool()
prevBanLoggerState = false
ReminderState = new.bool()
dateExpandedStates = {}
banSearchBuf = new.char[64]()
copyButtonAnimationTime = {}
copyButtonClickedDate = {}
showWelcomeAnimation = false
welcomeAnimationStartTime = 0
welcomeAnimationJustCompleted = false
returnAnimationShown = false
returnAnimationStartTime = 0
banMessage = new.char[128](u8'/ban {BotName} 30 чит')
UpdateWindowState = new.bool(false)
updateInfoLines = {}
updateTitleText = u8'Доступно обновление BBot'
updateAvailableVersion = nil
updateCheckInProgress = false
updateDownloadInProgress = false
updateDownloadCompleted = false
updateDownloadMessage = nil
updatePromptNotificationShown = false
versionFileProcessed = false
deferredUpdateVersion = ''

-- Поисковые режимы: 'idle' (как сейчас), 'serch' (последовательная проверка /re)
searchMode = 'idle'
currentSearchTargetId = nil
searchControllerThread = nil
banOccurredFlag = false

reminderStartTime = 0
reminderBotCount = 0
lastReminderCheckTime = 0
lastReminderShowTime = 0
QuickTPState = new.bool(true)
isAutoBan = new.bool(true)
banCountdownMs = new.int(4000)
lowDelayWarningState = new.bool(false)
lowDelayConfirmed = false
lowDelayPrevValue = 4000
lowDelayContinueEnabled = false
lowDelayContinueEnableTime = 0

-- Фоновый режим (работает как Idle, но без /re и окна)
backgroundMode = new.bool(false)
activationKey = new.int(0x52) -- R по умолчанию
waitingForActivationKey = false
backgroundPending = nil

banKey = new.int(0x42)
skipKey = new.int(0x4E)
prevBanKey = false
prevSkipKey = false
waitingForBanKey = false
waitingForSkipKey = false

hoverAlpha = new.float(0.85)
animationTime = 0.0
lastFrameTime = os.clock()

local function trim(str)
	if type(str) ~= 'string' then return '' end
	return (str:gsub('^%s+', ''):gsub('%s+$', ''))
end

function applyUiTheme()
	local style = imgui.GetStyle()

	style.WindowRounding = 12.0
	style.FrameRounding = 8.0
	style.GrabRounding = 8.0
	style.ScrollbarRounding = 10.0
	style.ChildRounding = 12.0
	style.PopupRounding = 12.0
	style.TabRounding = 8.0

	style.WindowBorderSize = 1.5
	style.FrameBorderSize = 1.0
	style.PopupBorderSize = 1.0

	style.WindowPadding = imgui.ImVec2(16, 16)

	style.FramePadding = imgui.ImVec2(12, 6)
	style.ItemSpacing = imgui.ImVec2(12, 10)
	style.ItemInnerSpacing = imgui.ImVec2(10, 8)
	style.WindowTitleAlign = imgui.ImVec2(0.5, 0.5)

	style.ButtonTextAlign = imgui.ImVec2(0.5, 0.5)

	style.Alpha = 1.0
	style.IndentSpacing = 21.0
	style.ScrollbarSize = 14.0
	style.GrabMinSize = 10.0

	local colors = style.Colors

	colors[imgui.Col.Text] = imgui.ImVec4(0.95, 0.96, 0.98, 1.00)
	colors[imgui.Col.TextDisabled] = imgui.ImVec4(0.50, 0.50, 0.52, 0.58)

	colors[imgui.Col.WindowBg] = imgui.ImVec4(0.06, 0.06, 0.08, 0.95)
	colors[imgui.Col.ChildBg] = imgui.ImVec4(0.08, 0.08, 0.10, 0.90)
	colors[imgui.Col.PopupBg] = imgui.ImVec4(0.07, 0.07, 0.09, 0.98)

	colors[imgui.Col.Border] = imgui.ImVec4(0.18, 0.18, 0.22, 0.80)
	colors[imgui.Col.BorderShadow] = imgui.ImVec4(0.00, 0.00, 0.00, 0.00)

	colors[imgui.Col.FrameBg] = imgui.ImVec4(0.12, 0.12, 0.15, 0.85)
	colors[imgui.Col.FrameBgHovered] = imgui.ImVec4(0.16, 0.16, 0.20, 0.90)
	colors[imgui.Col.FrameBgActive] = imgui.ImVec4(0.20, 0.20, 0.24, 0.95)

	colors[imgui.Col.TitleBg] = imgui.ImVec4(0.08, 0.08, 0.10, 1.00)
	colors[imgui.Col.TitleBgActive] = imgui.ImVec4(0.10, 0.10, 0.12, 1.00)
	colors[imgui.Col.TitleBgCollapsed] = imgui.ImVec4(0.08, 0.08, 0.10, 0.75)

	colors[imgui.Col.CheckMark] = imgui.ImVec4(0.65, 0.35, 1.00, 1.00)
	colors[imgui.Col.SliderGrab] = imgui.ImVec4(0.55, 0.30, 0.95, 1.00)
	colors[imgui.Col.SliderGrabActive] = imgui.ImVec4(0.70, 0.40, 1.00, 1.00)

	colors[imgui.Col.Button] = imgui.ImVec4(0.50, 0.28, 0.88, 0.85)
	colors[imgui.Col.ButtonHovered] = imgui.ImVec4(0.60, 0.35, 0.98, 0.95)
	colors[imgui.Col.ButtonActive] = imgui.ImVec4(0.70, 0.42, 1.00, 1.00)

	colors[imgui.Col.Header] = imgui.ImVec4(0.48, 0.26, 0.85, 0.80)
	colors[imgui.Col.HeaderHovered] = imgui.ImVec4(0.58, 0.32, 0.95, 0.90)
	colors[imgui.Col.HeaderActive] = imgui.ImVec4(0.68, 0.38, 1.00, 1.00)

	colors[imgui.Col.Separator] = imgui.ImVec4(0.20, 0.20, 0.25, 0.60)
	colors[imgui.Col.SeparatorHovered] = imgui.ImVec4(0.45, 0.25, 0.80, 0.75)
	colors[imgui.Col.SeparatorActive] = imgui.ImVec4(0.55, 0.30, 0.95, 1.00)


end

function DangerButton(label, size)

	local baseColor = imgui.ImVec4(0.85, 0.20, 0.22, 0.90)
	local hoverColor = imgui.ImVec4(0.95, 0.28, 0.30, 0.95)
	local activeColor = imgui.ImVec4(1.00, 0.35, 0.38, 1.00)
	
	imgui.PushStyleColor(imgui.Col.Button, baseColor)
	imgui.PushStyleColor(imgui.Col.ButtonHovered, hoverColor)
	imgui.PushStyleColor(imgui.Col.ButtonActive, activeColor)

	local clicked = imgui.Button(label, size)
	
	imgui.PopStyleColor(3)
	return clicked
end

function SecondaryButton(label, size)

	local baseColor = imgui.ImVec4(0.22, 0.22, 0.26, 0.80)
	local hoverColor = imgui.ImVec4(0.35, 0.30, 0.45, 0.90)
	local activeColor = imgui.ImVec4(0.42, 0.35, 0.52, 1.00)
	
	imgui.PushStyleColor(imgui.Col.Button, baseColor)
	imgui.PushStyleColor(imgui.Col.ButtonHovered, hoverColor)
	imgui.PushStyleColor(imgui.Col.ButtonActive, activeColor)

	local clicked = imgui.Button(label, size)
	
	imgui.PopStyleColor(3)
	return clicked
end

function AnimatedButton(label, size, baseColor, pulseSpeed)
	pulseSpeed = pulseSpeed or 2.0
	animationTime = animationTime + 0.02
	
	local pulse = 0.5 + 0.5 * math.sin(animationTime * pulseSpeed)
	local alpha = 0.75 + 0.20 * pulse
	
	local btnColor = imgui.ImVec4(
		baseColor.x * (0.9 + 0.1 * pulse),
		baseColor.y * (0.9 + 0.1 * pulse),
		baseColor.z * (0.9 + 0.1 * pulse),
		alpha
	)
	
	imgui.PushStyleColor(imgui.Col.Button, btnColor)
	imgui.PushStyleColor(imgui.Col.ButtonHovered, imgui.ImVec4(
		baseColor.x * 1.2,
		baseColor.y * 1.2,
		baseColor.z * 1.2,
		0.95
	))
	imgui.PushStyleColor(imgui.Col.ButtonActive, imgui.ImVec4(
		baseColor.x * 1.3,
		baseColor.y * 1.3,
		baseColor.z * 1.3,
		1.00
	))

	local clicked = imgui.Button(label, size)
	
	imgui.PopStyleColor(3)
	return clicked
end

themeApplied = false

copyToClipboard = (function()

	local user32, kernel32
	local loaded = false
	
	return function(text)
		if not text or text == '' then return false end

		if not loaded then
			local ok, err = pcall(function()
				ffi.cdef[[
					bool OpenClipboard(void* hWnd);
					bool CloseClipboard(void);
					bool EmptyClipboard(void);
					void* SetClipboardData(unsigned int uFormat, void* hMem);
					void* GlobalAlloc(unsigned int uFlags, size_t dwBytes);
					void* GlobalLock(void* hMem);
					bool GlobalUnlock(void* hMem);
					int MultiByteToWideChar(unsigned int CodePage, unsigned long dwFlags, const char* lpMultiByteStr, int cbMultiByte, wchar_t* lpWideCharStr, int cchWideChar);
				]]
				user32 = ffi.load('user32')
				kernel32 = ffi.load('kernel32')
				loaded = true
			end)
			if not ok then return false end
		end
		
		local CF_UNICODETEXT = 13
		local GMEM_MOVEABLE = 0x0002
		local CP_UTF8 = 65001

		local textBytes = ffi.new('char[?]', #text + 1)
		ffi.copy(textBytes, text, #text)
		textBytes[#text] = 0

		local textLen = #text
		local wTextLen = kernel32.MultiByteToWideChar(CP_UTF8, 0, textBytes, textLen, nil, 0)
		if wTextLen == 0 then return false end

		local memSize = (wTextLen + 1) * 2
		local hMem = kernel32.GlobalAlloc(GMEM_MOVEABLE, memSize)
		if hMem == nil then return false end

		local pMem = kernel32.GlobalLock(hMem)
		if pMem == nil then
			return false
		end

		local result = kernel32.MultiByteToWideChar(CP_UTF8, 0, textBytes, textLen, ffi.cast('wchar_t*', pMem), wTextLen)
		if result == 0 then
			kernel32.GlobalUnlock(hMem)
			return false
		end

		ffi.cast('wchar_t*', pMem)[wTextLen] = 0
		kernel32.GlobalUnlock(hMem)

		if user32.OpenClipboard(nil) then

			user32.EmptyClipboard()

			user32.SetClipboardData(CF_UNICODETEXT, hMem)
			user32.CloseClipboard()
			return true
		else
			return false
		end
	end
end)()

openUrl = (function()
	local shell32
	local loaded = false
	
	return function(url)
		if not url or url == '' then return false end

		if not loaded then
			local ok, err = pcall(function()
				ffi.cdef[[
					long ShellExecuteA(void* hwnd, const char* lpOperation, const char* lpFile, const char* lpParameters, const char* lpDirectory, int nShowCmd);
				]]
				shell32 = ffi.load('shell32')
				loaded = true
			end)
			if not ok then return false end
		end

		local result = shell32.ShellExecuteA(nil, "open", url, nil, nil, 1)

		return result > 32
	end
end)()

function getConfigDir()
	return getWorkingDirectory() .. "\\config\\BBot"
end

function getSettingsPath()
	return getConfigDir() .. "\\settings.txt"
end

function getVersionTempPath()
	return getConfigDir() .. "\\BbotVersion.ini"
end

local function deferUpdateReminder()
	if not updateAvailableVersion then return end
	deferredUpdateVersion = updateAvailableVersion
	saveSettings()
	showUpdateChatHint()
	UpdateWindowState[0] = false
end

local function showUpdateChatHint()
	if type(sampAddChatMessage) ~= 'function' then return end
	local text = u8('[BBot v2.0] Есть обновление! Для просмотра введите /bupdate')
	sampAddChatMessage(u8:decode(text, 'CP1251'), -1)
end

local function resetUpdateFlags()
	updateCheckInProgress = false
end

local function finalizeVersionCheck(remoteVersion, notes)
	if not remoteVersion or remoteVersion == '' then
		sendUpdateMessage('Файл версии получен, но строка с номером пустая.')
		resetUpdateFlags()
		return
	end

	if remoteVersion ~= CURRENT_VERSION then
		if deferredUpdateVersion ~= '' and deferredUpdateVersion ~= remoteVersion then
			deferredUpdateVersion = ''
			saveSettings()
		end
		updateAvailableVersion = remoteVersion
		updateTitleText = u8(string.format('BBot v%s — доступно обновление', remoteVersion))
		updateInfoLines = notes or {}
		if deferredUpdateVersion == remoteVersion then
			UpdateWindowState[0] = false
			showUpdateChatHint()
		else
			UpdateWindowState[0] = true
			if not updatePromptNotificationShown then
				addNotification(string.format(u8'Доступна версия %s. Открой окно обновления.', remoteVersion))
				updatePromptNotificationShown = true
			end
		end
		sendUpdateMessage(string.format('Найдена новая версия: %s (текущая: %s)', remoteVersion, CURRENT_VERSION))
	else
		updateAvailableVersion = nil
		updateInfoLines = {}
		updateTitleText = u8'BBot — обновления'
		UpdateWindowState[0] = false
		sendUpdateMessage('Проверка завершена: установлена актуальная версия.')
		if deferredUpdateVersion ~= '' then
			deferredUpdateVersion = ''
			saveSettings()
		end
	end
	resetUpdateFlags()
end

local function handleVersionFile(path)
	local file = io.open(path, "r")
	if not file then
		sendUpdateMessage('Не удалось открыть временный файл версии.')
		resetUpdateFlags()
		return
	end

	local lines = {}
	for line in file:lines() do
		line = line:gsub("^\239\187\191", "")
		line = line:gsub("\r", "")
		table.insert(lines, line)
		if #lines > 100 then break end
	end
	file:close()

	if #lines == 0 then
		sendUpdateMessage('Файл версии пустой.')
		resetUpdateFlags()
		return
	end

	local remoteVersion = trim(lines[1])
	sendUpdateMessage(string.format('Версия в файле: "%s"', remoteVersion ~= '' and remoteVersion or 'пусто'))
	local notes = {}
	for i = 2, #lines do
		local note = trim(lines[i])
		if note ~= '' then
			table.insert(notes, note)
		end
	end

	finalizeVersionCheck(remoteVersion, notes)
end

function checkForUpdates()
	if updateCheckInProgress then return end
	updateCheckInProgress = true
	versionFileProcessed = false
	sendUpdateMessage('Запускаю проверку обновлений...')

	local tempPath = getVersionTempPath()
	if doesFileExist(tempPath) then
		os.remove(tempPath)
	end

	downloadUrlToFile(VERSION_INFO_URL, tempPath, function(id, status)
		if status == dlstatus.STATUS_ENDDOWNLOADDATA then
			sendUpdateMessage('Файл версии скачан, начинаю разбор...')
			lua_thread.create(function()
				handleVersionFile(tempPath)
			end)
		elseif status == dlstatus.STATUSEX_ENDDOWNLOAD then
			if not doesFileExist(tempPath) then
				sendUpdateMessage('Загрузка файла версии завершилась с ошибкой.')
				resetUpdateFlags()
			end
		else
			sendUpdateMessage(string.format('Статус загрузки файла версии: %s', tostring(status)))
		end
	end)
end

local function finishUpdateDownload(success, message)
	updateDownloadInProgress = false
	if success then
		updateDownloadCompleted = true
		updateDownloadMessage = message or u8'Обновление успешно установлено.'
		sendUpdateMessage('Обновление скачано и сохранено. Перезапусти BBot.')
		if deferredUpdateVersion ~= '' then
			deferredUpdateVersion = ''
			saveSettings()
		end
	else
		updateDownloadCompleted = false
		updateDownloadMessage = message
		sendUpdateMessage(message and ('Ошибка обновления: ' .. message) or 'Не удалось загрузить обновление.')
	end
end

function startUpdateDownload()
	if updateDownloadInProgress then return end
	updateDownloadInProgress = true
	updateDownloadCompleted = false
	updateDownloadMessage = nil
	sendUpdateMessage(string.format('Начинаю скачивание версии %s...', updateAvailableVersion or '?'))

	local scriptInfo = thisScript()
	local scriptPath = scriptInfo and scriptInfo.path
	if not scriptPath or scriptPath == '' then
		finishUpdateDownload(false, u8'Не удалось определить путь скрипта.')
		sendUpdateMessage('Не удалось определить путь текущего скрипта.')
		return
	end

	downloadUrlToFile(SCRIPT_DOWNLOAD_URL, scriptPath, function(id, status)
		if status == dlstatus.STATUS_ENDDOWNLOADDATA then
			finishUpdateDownload(true, u8'Файл заменён. Перезапусти скрипт (/reloadall).')
			addNotification(u8'BBot обновлён. Перезапусти MoonLoader.')
		elseif status == dlstatus.STATUSEX_ENDDOWNLOAD then
			if not doesFileExist(scriptPath) then
				finishUpdateDownload(false, u8'Не удалось скачать файл обновления.')
			else
				sendUpdateMessage('Драйвер скачивания сообщил об окончании с предупреждением.')
			end
		else
			sendUpdateMessage(string.format('Статус загрузки обновления: %s', tostring(status)))
		end
	end)
end

function ensureConfigFile()
	local dir = getConfigDir()
	local path = getSettingsPath()
	if not doesDirectoryExist(dir) then
		createDirectory(dir)
	end
		if not doesFileExist(path) then
		local f = io.open(path, "w")
		if f then

			local raw = ffi.string(banMessage) or ""
			f:write("BanMessage=" .. raw .. "\n")
			f:write("BanKey=66\n")
			f:write("SkipKey=78\n")
			f:write("BanCountdownMs=4000\n")
			f:write("ShowWelcomeAnimation=false\n")
			f:write("IsAutoBan=true\n")
			f:write("SearchMode=idle\n")
			f:write("BackgroundMode=false\n")
			f:write("ActivationKey=82\n")
			f:write("DeferredUpdateVersion=\n")
			f:close()
		end
	end
	return path
end

function setBufferFromString(buf, str)
    local size = ffi.sizeof(buf)
    ffi.fill(buf, size)
    if not str then return end
    local toCopy = math.min(#str, size - 1)
    if toCopy > 0 then ffi.copy(buf, str, toCopy) end
end

function setBanMessageFromString(str)
    setBufferFromString(banMessage, str)
end

function isValidUtf8(str)
	if type(str) ~= 'string' then return false end
	local i, len = 1, #str
	while i <= len do
		local c = str:byte(i)
		if c < 0x80 then
			i = i + 1
		elseif c >= 0xC2 and c <= 0xDF then
			if i + 1 > len then return false end
			local c2 = str:byte(i + 1)
			if c2 < 0x80 or c2 > 0xBF then return false end
			i = i + 2
		elseif c >= 0xE0 and c <= 0xEF then
			if i + 2 > len then return false end
			local c2, c3 = str:byte(i + 1), str:byte(i + 2)
			if c == 0xE0 then if c2 < 0xA0 or c2 > 0xBF then return false end
			elseif c == 0xED then if c2 < 0x80 or c2 > 0x9F then return false end
			else if c2 < 0x80 or c2 > 0xBF then return false end end
			if c3 < 0x80 or c3 > 0xBF then return false end
			i = i + 3
		elseif c >= 0xF0 and c <= 0xF4 then
			if i + 3 > len then return false end
			local c2, c3, c4 = str:byte(i + 1), str:byte(i + 2), str:byte(i + 3)
			if c == 0xF0 then if c2 < 0x90 or c2 > 0xBF then return false end
			elseif c == 0xF4 then if c2 < 0x80 or c2 > 0x8F then return false end
			else if c2 < 0x80 or c2 > 0xBF then return false end end
			if c3 < 0x80 or c3 > 0xBF or c4 < 0x80 or c4 > 0xBF then return false end
			i = i + 4
		else
			return false
		end
	end
	return true
end

function loadSettings()
	local path = ensureConfigFile()
	local f = io.open(path, "r")
	if not f then return end
	for line in f:lines() do
		local key, value = line:match("^(%w+)%s*=%s*(.*)$")
		if key == 'BanMessage' and value then
			setBanMessageFromString(value)
		elseif key == 'BanKey' and value then
			local v = tonumber(value)
			if v then banKey[0] = v end
		elseif key == 'SkipKey' and value then
			local v = tonumber(value)
			if v then skipKey[0] = v end
		elseif key == 'BanCountdownMs' and value then
			local v = tonumber(value)
			if v then
				banCountdownMs[0] = v

				if v < 3000 then
					lowDelayConfirmed = false
				else
					lowDelayConfirmed = true
				end
			end
		elseif key == 'ShowWelcomeAnimation' and value then

			local v = value:lower()
			if v == "true" or v == "1" then
				showWelcomeAnimation = true
			else
				showWelcomeAnimation = false
			end
		elseif key == 'IsAutoBan' and value then

			local v = value:lower()
			if v == "true" or v == "1" then
				isAutoBan[0] = true
			else
				isAutoBan[0] = false
			end
		elseif key == 'SearchMode' and value then
			local v = value:lower()
			if v == 'serch' then
				searchMode = 'serch'
			else
				searchMode = 'idle'
			end
		elseif key == 'BackgroundMode' and value then
			local v = value:lower()
			if v == 'true' or v == '1' then
				backgroundMode[0] = true
			else
				backgroundMode[0] = false
			end
		elseif key == 'ActivationKey' and value then
			local v = tonumber(value)
			if v then activationKey[0] = v end
		elseif key == 'DeferredUpdateVersion' and value then
			deferredUpdateVersion = value
		end
	end
	f:close()
end

function saveSettings()
	local path = ensureConfigFile()
	local f = io.open(path, "w")
	if not f then return end
	local raw = ffi.string(banMessage)
	if raw == nil or raw == '' then raw = u8'Забанил' end

	f:write("BanMessage=" .. raw .. "\n")
	f:write("BanKey=" .. banKey[0] .. "\n")
	f:write("SkipKey=" .. skipKey[0] .. "\n")
	f:write("BanCountdownMs=" .. banCountdownMs[0] .. "\n")
	f:write("ShowWelcomeAnimation=" .. tostring(showWelcomeAnimation) .. "\n")
	f:write("IsAutoBan=" .. tostring(isAutoBan[0]) .. "\n")
	f:write("SearchMode=" .. tostring(searchMode) .. "\n")
	f:write("BackgroundMode=" .. tostring(backgroundMode[0]) .. "\n")
	f:write("ActivationKey=" .. tostring(activationKey[0]) .. "\n")
	f:write("DeferredUpdateVersion=" .. tostring(deferredUpdateVersion or '') .. "\n")
	f:close()
end

function getCoordsPath()
	return getConfigDir() .. "\\cords.txt"
end

function ensureCoordsFile()
	local path = getCoordsPath()
	local legacy = getConfigDir() .. "\\cords"

	if not doesFileExist(path) and doesFileExist(legacy) then
		os.rename(legacy, path)
	end
	if not doesFileExist(path) then
		local f = io.open(path, "w")
		if f then

			f:write("\239\187\191")
			f:write(u8:encode('Ферма|-103.05|106.17|8.12') .. '\n')
			f:write(u8:encode('Респа 1|1750.88|-1892.53|29.24') .. '\n')
			f:write(u8:encode('Респа 2|1153.03|-1762.28|21.84') .. '\n')
			f:write(u8:encode('Завод|-86.12|-298.01|16.42') .. '\n')
			f:close()
		end
	end
	return path
end

function loadCoords()
	local path = ensureCoordsFile()
	local f = io.open(path, 'r')
	if not f then return end
	teleportCoords = {}
	teleportNames = {}
	for line in f:lines() do

		line = line:gsub("^\239\187\191", "")
		local name, sx, sy, sz = line:match("^([^|]+)|%s*(-?[%n%d%.]+)|%s*(-?[%n%d%.]+)|%s*(-?[%n%d%.]+)%s*$")
		if name and sx and sy and sz then
			local x = tonumber(sx)
			local y = tonumber(sy)
			local z = tonumber(sz)
			if x and y and z then

				local idx = #teleportCoords + 1
				table.insert(teleportCoords, { x = x, y = y, z = z })
				teleportNames[idx] = new.char[64](name)
			end
		end
	end
	f:close()

end

function saveCoords()
	local path = ensureCoordsFile()
	local f = io.open(path, 'w')
	if not f then return end

	f:write("\239\187\191")
	for i, coord in ipairs(teleportCoords) do
		local nm = teleportNames[i] and ffi.string(teleportNames[i]) or string.format('Точка %d', i)
		if not isValidUtf8(nm) then nm = u8:encode(nm) end
		f:write(string.format("%s|%.2f|%.2f|%.2f\n", nm, coord.x, coord.y, coord.z))
	end
	f:close()
end

function getBansPath()
	return getConfigDir() .. "\\bans.txt"
end

function ensureBansFile()
	local path = getBansPath()
	if not doesFileExist(path) then
		local f = io.open(path, "w")
		if f then

			f:write("\239\187\191")
			f:close()
		end
	end
	return path
end

function logBan(playerName, reTime)
	if not playerName or playerName == '' then return end
	local path = ensureBansFile()
	local f = io.open(path, "a")
	if f then

		local timestamp = os.date("%Y-%m-%d %H:%M:%S")

		local timeDiff = ""
		if reTime then
			local currentTime = os.clock()
			local diffSeconds = currentTime - reTime
			if diffSeconds >= 0 then

				if diffSeconds < 60 then
					timeDiff = string.format("%.2fс", diffSeconds)
				else
					local minutes = math.floor(diffSeconds / 60)
					local seconds = diffSeconds % 60
					timeDiff = string.format("%dм %.2fс", minutes, seconds)
				end
			end
		end

		local logLine = string.format("%s|%s|%s\n", playerName, timestamp, timeDiff)
		f:write(u8:encode(logLine, 'CP1251'))
		f:close()
	end
end

function loadBans()
	local bans = {}
	local path = getBansPath()
	if not doesFileExist(path) then
		return bans
	end
	local f = io.open(path, "r")
	if not f then return bans end
	for line in f:lines() do

		line = line:gsub("^\239\187\191", "")

		local decodedLine = u8:decode(line, 'CP1251')

		local name, timestamp, timeDiff = decodedLine:match("^([^|]+)|([^|]+)|([^|]*)%s*$")
		if name and timestamp then
			table.insert(bans, {
				name = name,
				timestamp = timestamp,
				timeDiff = timeDiff or ""
			})
		end
	end
	f:close()

	local reversed = {}
	for i = #bans, 1, -1 do
		table.insert(reversed, bans[i])
	end
	return reversed
end

function formatDateToRussian(dateStr)

	local year, month, day = dateStr:match("^(%d%d%d%d)%-(%d%d)%-(%d%d)$")
	if not year or not month or not day then
		return dateStr
	end
	
	year = tonumber(year)
	month = tonumber(month)
	day = tonumber(day)

	local monthNames = {
		[1] = "января", [2] = "февраля", [3] = "марта", [4] = "апреля",
		[5] = "мая", [6] = "июня", [7] = "июля", [8] = "августа",
		[9] = "сентября", [10] = "октября", [11] = "ноября", [12] = "декабря"
	}

	local dayNames = {
		[1] = "Первое", [2] = "Второе", [3] = "Третье", [4] = "Четвертое",
		[5] = "Пятое", [6] = "Шестое", [7] = "Седьмое", [8] = "Восьмое",
		[9] = "Девятое", [10] = "Десятое", [11] = "Одиннадцатое", [12] = "Двенадцатое",
		[13] = "Тринадцатое", [14] = "Четырнадцатое", [15] = "Пятнадцатое",
		[16] = "Шестнадцатое", [17] = "Семнадцатое", [18] = "Восемнадцатое",
		[19] = "Девятнадцатое", [20] = "Двадцатое", [21] = "Двадцать первое",
		[22] = "Двадцать второе", [23] = "Двадцать третье", [24] = "Двадцать четвертое",
		[25] = "Двадцать пятое", [26] = "Двадцать шестое", [27] = "Двадцать седьмое",
		[28] = "Двадцать восьмое", [29] = "Двадцать девятое", [30] = "Тридцатое",
		[31] = "Тридцать первое"
	}
	
	local monthName = monthNames[month] or month
	local dayName = dayNames[day] or tostring(day)
	
	return string.format("%s %s %d года", dayName, monthName, year)
end

function getBanWord(count)
	local lastDigit = count % 10
	local lastTwoDigits = count % 100

	if lastTwoDigits >= 11 and lastTwoDigits <= 14 then
		return "банов"

	elseif lastDigit == 1 then
		return "бан"

	elseif lastDigit >= 2 and lastDigit <= 4 then
		return "бана"

	else
		return "банов"
	end
end

function getBotWord(count)
	local lastDigit = count % 10
	local lastTwoDigits = count % 100

	if lastTwoDigits >= 11 and lastTwoDigits <= 14 then
		return "ботов"

	elseif lastDigit == 1 then
		return "бот"

	elseif lastDigit >= 2 and lastDigit <= 4 then
		return "бота"

	else
		return "ботов"
	end
end

function groupBansByDate(bans)
	local grouped = {}
	for _, ban in ipairs(bans) do

		local date = ban.timestamp:match("^(%d%d%d%d%-%d%d%-%d%d)")
		if date then
			if not grouped[date] then
				grouped[date] = {}
			end
			table.insert(grouped[date], ban)
		end
	end

	local result = {}
	local dates = {}
	for date, _ in pairs(grouped) do
		table.insert(dates, date)
	end
	table.sort(dates, function(a, b) return a > b end)
	for _, date in ipairs(dates) do
		table.insert(result, { date = date, bans = grouped[date] })
	end
	return result
end

function performBan()
	if not pendingReport then return end
	
	sampSendChat("/reoff")
	local raw = ffi.string(banMessage)
	if raw == nil or raw == '' then raw = u8'Забанил' end
	local playerName = nil
	local reTime = nil
	if pendingReport and pendingReport.name then
		playerName = pendingReport.name
		reTime = pendingReport.reTime
		raw = raw:gsub("{BotName}", playerName)
	else
		raw = raw:gsub("{BotName}", "")
	end
	local msg = u8:decode(raw)
	sampSendChat(msg)

	if playerName then
		logBan(playerName, reTime)
		local decodedName = u8:decode(playerName, 'CP1251')
		addNotification(string.format(u8'Забанил %s', decodedName))
	end
	DecisionOpen[0] = false
	pendingReport = nil
	isProcessing = false
	lastDecisionCloseTime = os.clock() * 1000
    banOccurredFlag = true
end

imgui.OnFrame(function() return UpdateWindowState[0] end, function(player)
	if not themeApplied then
		applyUiTheme()
		themeApplied = true
	end

	local infoCount = updateInfoLines and #updateInfoLines or 0
	local lineHeight = imgui.GetTextLineHeightWithSpacing()
	local notesHeight = math.min(320.0, math.max(120.0, lineHeight * math.max(infoCount, 1) + 40.0))
	local minWindowHeight = 320.0
	local maxWindowHeight = 620.0
	local computedHeight = math.max(minWindowHeight, math.min(maxWindowHeight, 180.0 + notesHeight))

	imgui.SetNextWindowPos(imgui.ImVec2(520, 260), imgui.Cond.FirstUseEver, imgui.ImVec2(0.5, 0.5))
	imgui.SetNextWindowSize(imgui.ImVec2(520, computedHeight), imgui.Cond.Always)
	imgui.Begin(updateTitleText, UpdateWindowState, imgui.WindowFlags.NoCollapse + imgui.WindowFlags.NoScrollbar + imgui.WindowFlags.NoResize)

	imgui.Text(u8(string.format('Текущая версия: %s', CURRENT_VERSION)))
	if updateAvailableVersion then
		imgui.SameLine()
		imgui.Text(u8(string.format('Новая версия: %s', updateAvailableVersion)))
	else
		imgui.SameLine()
		imgui.Text(u8'Обновления не найдены')
	end

	imgui.Dummy(imgui.ImVec2(0, 8))
	imgui.Separator()
	imgui.Dummy(imgui.ImVec2(0, 6))
	imgui.Text(u8'Список изменений:')
	imgui.Dummy(imgui.ImVec2(0, 4))

	imgui.BeginChild('##update_notes', imgui.ImVec2(0, notesHeight), false, imgui.WindowFlags.NoScrollbar)
	if updateInfoLines and #updateInfoLines > 0 then
		for _, line in ipairs(updateInfoLines) do
			imgui.Text(u8(line))
		end
	else
		imgui.Text(u8'Описание обновления отсутствует.')
	end
	imgui.EndChild()

	imgui.Dummy(imgui.ImVec2(0, 10))
	if updateDownloadMessage then
		local color = updateDownloadCompleted and imgui.ImVec4(0.30, 0.75, 0.40, 1.0) or imgui.ImVec4(0.95, 0.35, 0.38, 1.0)
		imgui.TextColored(color, updateDownloadMessage)
		imgui.Dummy(imgui.ImVec2(0, 6))
	end

	local buttonWidth = 200
	local buttonSpacing = 12
	local totalWidth = buttonWidth * 2 + buttonSpacing
	local regionWidth = imgui.GetWindowContentRegionWidth()
	local offsetX = math.max(0, (regionWidth - totalWidth) * 0.5)
	imgui.SetCursorPosX(imgui.GetCursorPosX() + offsetX)

	if updateDownloadInProgress then
		imgui.Text(u8'Скачивание обновления, пожалуйста подождите...')
	else
		if updateAvailableVersion then
			local baseColor = imgui.ImVec4(0.30, 0.70, 0.40, 0.90)
			local clicked = AnimatedButton(u8'Обновить сейчас', imgui.ImVec2(buttonWidth, 34), baseColor, 1.5)
			if clicked then
				startUpdateDownload()
			end
			imgui.SameLine(0, buttonSpacing)
			if SecondaryButton(u8'Позже', imgui.ImVec2(buttonWidth, 34)) then
				deferUpdateReminder()
			end
		else
			if SecondaryButton(u8'Закрыть', imgui.ImVec2(buttonWidth, 34)) then
				UpdateWindowState[0] = false
			end
		end
	end

	imgui.End()
end)


imgui.OnFrame(function() return WinState[0] end, function(player)
	if not themeApplied then
		applyUiTheme()
		themeApplied = true
	end

	if not showWelcomeAnimation and welcomeAnimationStartTime == 0 then
		welcomeAnimationStartTime = os.clock()
		welcomeAnimationJustCompleted = false
	elseif showWelcomeAnimation and not returnAnimationShown and returnAnimationStartTime == 0 and not welcomeAnimationJustCompleted then


		returnAnimationStartTime = os.clock()
	end
	
	imgui.SetNextWindowPos(imgui.ImVec2(500,200), imgui.Cond.FirstUseEver, imgui.ImVec2(0.5, 0.5))
	    imgui.SetNextWindowSize(imgui.ImVec2(980, 740), imgui.Cond.Always)
	imgui.Begin(u8'BBot v2.0, давай побаним вместе!', WinState, imgui.WindowFlags.NoResize + imgui.WindowFlags.NoCollapse)

	    local isAnimationPlaying = false
	    local uiAlpha = 1.0
	    local uiFadeInDuration = 0.8
	    
	    if not showWelcomeAnimation and welcomeAnimationStartTime > 0 then

		    local currentTime = os.clock()
		    local elapsed = currentTime - welcomeAnimationStartTime
		    local fadeInDuration = 0.5
		    local showDuration = 6.0
		    local fadeOutDuration = 0.5
		    local totalDuration = fadeInDuration + showDuration + fadeOutDuration
		    
		    if elapsed < totalDuration then

			    isAnimationPlaying = true
			    uiAlpha = 0.0
		    else

			    local timeSinceAnimationEnd = elapsed - totalDuration
			    if timeSinceAnimationEnd < uiFadeInDuration then

				    uiAlpha = timeSinceAnimationEnd / uiFadeInDuration
			    else

				    uiAlpha = 1.0
			    end
		    end
	    elseif showWelcomeAnimation and returnAnimationStartTime > 0 and not returnAnimationShown then

		    local currentTime = os.clock()
		    local elapsed = currentTime - returnAnimationStartTime
		    local fadeInDuration = 0.5
		    local showDuration = 1.5
		    local fadeOutDuration = 0.5
		    local totalDuration = fadeInDuration + showDuration + fadeOutDuration
		    
		    if elapsed < totalDuration then

			    isAnimationPlaying = true
			    uiAlpha = 0.0
		    else

			    local timeSinceAnimationEnd = elapsed - totalDuration
			    if timeSinceAnimationEnd < uiFadeInDuration then

				    uiAlpha = timeSinceAnimationEnd / uiFadeInDuration
			    else

				    uiAlpha = 1.0
			    end

			    returnAnimationShown = true
		    end
	    else

		    uiAlpha = 1.0
	    end

	    if not isAnimationPlaying then

		    local style = imgui.GetStyle()
		    local originalChildBg = style.Colors[imgui.Col.ChildBg]
		    local originalText = style.Colors[imgui.Col.Text]
		    local originalFrameBg = style.Colors[imgui.Col.FrameBg]
		    local originalButton = style.Colors[imgui.Col.Button]
		    local originalButtonHovered = style.Colors[imgui.Col.ButtonHovered]
		    local originalButtonActive = style.Colors[imgui.Col.ButtonActive]
		    
		    imgui.PushStyleColor(imgui.Col.ChildBg, imgui.ImVec4(
			    originalChildBg.x, originalChildBg.y, originalChildBg.z, originalChildBg.w * uiAlpha
		    ))
		    imgui.PushStyleColor(imgui.Col.Text, imgui.ImVec4(
			    originalText.x, originalText.y, originalText.z, originalText.w * uiAlpha
		    ))
		    imgui.PushStyleColor(imgui.Col.FrameBg, imgui.ImVec4(
			    originalFrameBg.x, originalFrameBg.y, originalFrameBg.z, originalFrameBg.w * uiAlpha
		    ))
		    imgui.PushStyleColor(imgui.Col.Button, imgui.ImVec4(
			    originalButton.x, originalButton.y, originalButton.z, originalButton.w * uiAlpha
		    ))
		    imgui.PushStyleColor(imgui.Col.ButtonHovered, imgui.ImVec4(
			    originalButtonHovered.x, originalButtonHovered.y, originalButtonHovered.z, originalButtonHovered.w * uiAlpha
		    ))
		    imgui.PushStyleColor(imgui.Col.ButtonActive, imgui.ImVec4(
			    originalButtonActive.x, originalButtonActive.y, originalButtonActive.z, originalButtonActive.w * uiAlpha
		    ))

		    local mainAvail = imgui.GetContentRegionAvail()
		    local outerSidePadding = 12
		    local leftColWidth = math.floor((mainAvail.x - outerSidePadding * 3) / 2)

		    local reservedForSocialButtons = 80.0
		    local columnsHeight = mainAvail.y - reservedForSocialButtons
		    imgui.SetCursorPosX(imgui.GetCursorPosX() + outerSidePadding)
		    
		    imgui.BeginChild('##col_left', imgui.ImVec2(leftColWidth, columnsHeight), false, imgui.WindowFlags.NoScrollbar)

		    local avail = imgui.GetContentRegionAvail()
		    local sidePadding = 12
		    local bottomButtonHeight = 32.0
		    local reservedForButton = bottomButtonHeight + 30.0
		    local cardHeight = avail.y - reservedForButton
		    imgui.SetCursorPosX(imgui.GetCursorPosX() + sidePadding)
		    
		    imgui.BeginChild('##card_main', imgui.ImVec2(avail.x - sidePadding * 2, cardHeight), true, imgui.WindowFlags.NoScrollbar)

	local label = isRunning and u8'Стоп' or u8'Начать'
	local fullWidth = imgui.GetContentRegionAvail().x

	local mainButtonColor = isRunning and 
		imgui.ImVec4(0.85, 0.20, 0.22, 0.90) or
		imgui.ImVec4(0.30, 0.70, 0.40, 0.90)

	animationTime = animationTime + 0.03
	local pulse = 0.92 + 0.08 * math.sin(animationTime * 1.5)
	
	local animColor = imgui.ImVec4(
		mainButtonColor.x * pulse,
		mainButtonColor.y * pulse,
		mainButtonColor.z * pulse,
		mainButtonColor.w
	)
	
	imgui.PushStyleColor(imgui.Col.Button, animColor)
	imgui.PushStyleColor(imgui.Col.ButtonHovered, imgui.ImVec4(
		mainButtonColor.x * 1.15,
		mainButtonColor.y * 1.15,
		mainButtonColor.z * 1.15,
		0.95
	))
	imgui.PushStyleColor(imgui.Col.ButtonActive, imgui.ImVec4(
		mainButtonColor.x * 1.25,
		mainButtonColor.y * 1.25,
		mainButtonColor.z * 1.25,
		1.00
	))

	if imgui.Button(label, imgui.ImVec2(fullWidth, 38)) then
		if not isRunning then
			isRunning = true
			addNotification(u8'Начал искать')
			WinState[0] = false
			lastPlayerFoundAt = os.clock()
				scannerThread = lua_thread.create(function()
				while isRunning do
					local nowTime = os.clock()
					local myX, myY, myZ = getCharCoordinates(PLAYER_PED)
					local pcallOk, sampOk, myId = pcall(sampGetPlayerIdByCharHandle, PLAYER_PED)
					-- В режиме 'idle' сканируем всех, в 'serch' — только текущую цель (объявление ДО возможного goto)
					startId, endId, step = 0, 1000, 1
					if searchMode == 'serch' then
						if currentSearchTargetId ~= nil then
							startId, endId = currentSearchTargetId, currentSearchTargetId
						else
							startId, endId = 1, 0 -- пропустить цикл
						end
					end
					if not pcallOk or not sampOk or not myId then
						wait(100)
						goto continue_loop
					end

					for i = startId, endId, step do
						if sampIsPlayerConnected(i) and i ~= myId then
							local ok, ped = sampGetCharHandleBySampPlayerId(i)
							if ok then
								local px, py, pz = getCharCoordinates(ped)

								local last = playerLastPos[i]
								local speedKmh = nil
								if last ~= nil then
									local dt = nowTime - last.t
									if dt > 0 then
										local dx, dy, dz = px - last.x, py - last.y, pz - last.z
										local dist = math.sqrt(dx*dx + dy*dy + dz*dz)
										local mps = dist / dt
										speedKmh = mps * 3.6
									end
								end
								playerLastPos[i] = { x = px, y = py, z = pz, t = nowTime }

								if speedKmh ~= nil and speedKmh > 500.0 and not isCharInAnyCar(ped) then
									local dxm, dym, dzm = myX - px, myY - py, myZ - pz
									local distanceToMe = math.sqrt(dxm*dxm + dym*dym + dzm*dzm)
									if distanceToMe <= 300.0 then
										local level = sampGetPlayerScore(i)
										if level >= 1 and level <= 5 then

											lastPlayerFoundAt = nowTime

											local lastTriggerTime = triggeredInRadiusTime[i] or 0
											if (nowTime - lastTriggerTime) >= 10.0 then
												triggeredInRadius[i] = nil
												triggeredInRadiusTime[i] = nil
											end
											
																						if not triggeredInRadius[i] then
												local lastTrig = playerLastTriggeredAt[i] or 0
												if (nowTime - lastTrig) >= 1.0 and not isProcessing then
													triggeredInRadius[i] = true
													triggeredInRadiusTime[i] = nowTime
													playerLastTriggeredAt[i] = nowTime
													isProcessing = true
													local name = sampGetPlayerNickname(i)
													local decodedName = u8:decode(name, 'CP1251')
													addNotification(string.format(u8'Нашел %s', decodedName))

                                                    if backgroundMode[0] and not isRunning then
                                                        -- Фоновый режим: не начинаем слежку, показываем подсказку и сохраняем кандидата
                                                        backgroundPending = { id = i, name = name, level = level, distance = distanceToMe }
                                                        local keyName = vkeys.id_to_name(activationKey[0]) or string.format("0x%02X", activationKey[0])
                                                        local decodedName = u8:decode(name, 'CP1251')
                                                        addNotification(string.format(u8'%s возможно бот — нажмите %s', decodedName, keyName))
                                                        isProcessing = false
                                                    else
                                                                    if backgroundMode[0] and not isRunning then
                                                                        backgroundPending = { id = i, name = name, level = level, distance = distanceToMe }
                                                                        local keyName = vkeys.id_to_name(activationKey[0]) or string.format("0x%02X", activationKey[0])
                                                                        local decodedName = u8:decode(name, 'CP1251')
                                                                        addNotification(string.format(u8'%s возможно бот — нажмите %s', decodedName, keyName))
                                                                        isProcessing = false
                                                                    else
                                                                        local currentTime = os.clock() * 1000
                                                                        local reTime = nil
                                                                        if (currentTime - lastCommandTime) >= commandCooldown and (currentTime - lastDecisionCloseTime) >= 500 then
                                                                            sampSendChat(string.format("/re %s", name))
                                                                            lastCommandTime = currentTime
                                                                            reTime = os.clock()
                                                                            reCommandTime = os.clock()
                                                                        end

                                                                        pendingReport = { id = i, name = name, level = level, distance = distanceToMe, ip = "неизвестно", reTime = reTime }
                                                                        DecisionOpen[0] = true
                                                                        wasKickedFromSpectate = false
                                                                        banCountdownStartTime = os.clock()
                                                                        autoBanTriggered = false
                                                                    end
                                                    end

													wait(500)

													if not wasSpectating then
														wasSpectating = true
													end
													while DecisionOpen[0] do

														if wasKickedFromSpectate then

															if DecisionOpen[0] then
																sampSendChat("/reoff")
																DecisionOpen[0] = false
																isProcessing = false
																pendingReport = nil
																wasKickedFromSpectate = false
																wasSpectating = false
																lastDecisionCloseTime = os.clock() * 1000
															end
															break
														end
														wait(10)
													end
													isProcessing = false
												end
											end
										end
									else
										triggeredInRadius[i] = nil
										triggeredInRadiusTime[i] = nil
									end
								elseif isCharInAnyCar(ped) then
									-- Проверка игроков в машине на телепорт
									local lastCheckTime = playerInCarLastCheckTime[i] or 0
									local timeSinceLastCheck = (nowTime - lastCheckTime) * 1000.0 -- в миллисекундах
									
									-- Проверяем каждые 10мс
									if timeSinceLastCheck >= 10.0 then
										if not playerInCarPositions[i] then
											playerInCarPositions[i] = {}
										end
										
										-- Сохраняем текущую позицию
										table.insert(playerInCarPositions[i], { x = px, y = py, z = pz, t = nowTime })
										
										-- Оставляем только последние 2 позиции для проверки
										if #playerInCarPositions[i] > 2 then
											table.remove(playerInCarPositions[i], 1)
										end
										
										-- Проверяем расстояние между позициями если есть минимум 2 позиции
										if #playerInCarPositions[i] >= 2 then
											local prevPos = playerInCarPositions[i][#playerInCarPositions[i] - 1]
											local currPos = playerInCarPositions[i][#playerInCarPositions[i]]
											local dt = currPos.t - prevPos.t
											
											if dt > 0 then
												local dx = currPos.x - prevPos.x
												local dy = currPos.y - prevPos.y
												local dz = currPos.z - prevPos.z
												local distance = math.sqrt(dx*dx + dy*dy + dz*dz)
												
												-- Если расстояние слишком большое - это телепорт
												if distance > teleportDetectionDistance then
													local dxm, dym, dzm = myX - px, myY - py, myZ - pz
													local distanceToMe = math.sqrt(dxm*dxm + dym*dym + dzm*dzm)
													if distanceToMe <= 300.0 then
														local level = sampGetPlayerScore(i)
														if level >= 1 and level <= 5 then
															-- Сбрасываем триггер если прошло 10 секунд
															local lastTriggerTime = triggeredInRadiusTime[i] or 0
															if (nowTime - lastTriggerTime) >= 10.0 then
																playerInCarTriggered[i] = nil
															end
															
															if not playerInCarTriggered[i] then
																local lastTrig = playerLastTriggeredAt[i] or 0
																if (nowTime - lastTrig) >= 1.0 and not isProcessing then
																	playerInCarTriggered[i] = true
																	triggeredInRadiusTime[i] = nowTime
																	playerLastTriggeredAt[i] = nowTime
																	isProcessing = true
																	local name = sampGetPlayerNickname(i)
																	local decodedName = u8:decode(name, 'CP1251')
																	addNotification(string.format(u8'Нашел %s (в машине)', decodedName))

																	local currentTime = os.clock() * 1000
																	local reTime = nil
																	if (currentTime - lastCommandTime) >= commandCooldown and (currentTime - lastDecisionCloseTime) >= 500 then
																		sampSendChat(string.format("/re %s", name))
																		lastCommandTime = currentTime
																		reTime = os.clock()
																		reCommandTime = os.clock()
																	end

																	pendingReport = { id = i, name = name, level = level, distance = distanceToMe, ip = "неизвестно", reTime = reTime }
																	DecisionOpen[0] = true
																	wasKickedFromSpectate = false
																	banCountdownStartTime = os.clock()
																	autoBanTriggered = false

																	wait(500)

																	if not wasSpectating then
																		wasSpectating = true
																	end
																	while DecisionOpen[0] do
																		if wasKickedFromSpectate then
																			if DecisionOpen[0] then
																				sampSendChat("/reoff")
																				DecisionOpen[0] = false
																				isProcessing = false
																				pendingReport = nil
																				wasKickedFromSpectate = false
																				wasSpectating = false
																				lastDecisionCloseTime = os.clock() * 1000
																			end
																			break
																		end
																		wait(10)
																	end
																	isProcessing = false
																	playerInCarTriggered[i] = nil
																end
															end
														end
													else
														-- Игрок в машине слишком далеко - очищаем триггер
														playerInCarTriggered[i] = nil
													end
												end
											end
										end
										
										playerInCarLastCheckTime[i] = nowTime
									end
								else
									-- Игрок не в машине и не с высокой скоростью - очищаем данные
									playerInCarPositions[i] = nil
									playerInCarLastCheckTime[i] = nil
									playerInCarTriggered[i] = nil
								end
							end
						end
					end



					::continue_loop::

					local leftDown = isKeyDown(0x25)
					local rightDown = isKeyDown(0x27)
                    if searchMode == 'idle' and rightDown and not prevRightDown and not isProcessing and #teleportCoords > 0 and not sampIsChatInputActive() then
						local coord = teleportCoords[teleportIndex]

						local currentTime = os.clock() * 1000
						if (currentTime - lastCommandTime) >= commandCooldown then
							sampSendChat(string.format("/gc %.2f %.2f %.2f 0 0", coord.x, coord.y, coord.z))
							lastCommandTime = currentTime

					local pointName = teleportNames[teleportIndex] and ffi.string(teleportNames[teleportIndex]) or string.format('Точка %d', teleportIndex)

					local notificationText = string.format(u8'Телепортировался к: %s', pointName)
					addNotification(notificationText)
						end
						teleportIndex = teleportIndex + 1
						if teleportIndex > #teleportCoords then teleportIndex = 1 end
						lastPlayerFoundAt = os.clock()
					end
                    if searchMode == 'idle' and leftDown and not prevLeftDown and not isProcessing and #teleportCoords > 0 and not sampIsChatInputActive() then
						teleportIndex = teleportIndex - 1
						if teleportIndex < 1 then teleportIndex = #teleportCoords end
						local coord = teleportCoords[teleportIndex]

						local currentTime = os.clock() * 1000
						if (currentTime - lastCommandTime) >= commandCooldown then
							sampSendChat(string.format("/gc %.2f %.2f %.2f 0 0", coord.x, coord.y, coord.z))
							lastCommandTime = currentTime

					local pointName = teleportNames[teleportIndex] and ffi.string(teleportNames[teleportIndex]) or string.format('Точка %d', teleportIndex)

					local notificationText = string.format(u8'Телепортировался к %s', pointName)
					addNotification(notificationText)
						end
						lastPlayerFoundAt = os.clock()
					end
					prevLeftDown = leftDown
					prevRightDown = rightDown

					if (os.clock() * 1000 - lastCommandTime) < commandCooldown then
						wait(50)
					else
						wait(1)
					end
				end
			end)

			-- Контроллер режима 'serch': последовательно вызывает /re на игроков 1-5 уровня
			if searchMode == 'serch' then
				currentSearchTargetId = nil
				if searchControllerThread == nil then
					searchControllerThread = lua_thread.create(function()
						while isRunning and searchMode == 'serch' do
                            -- сформировать список кандидатов (единожды на цикл)
                            local candidates = {}
                            for i = 0, 1000 do
                                if sampIsPlayerConnected(i) then
                                    local lvl = sampGetPlayerScore(i)
                                    if lvl >= 1 and lvl <= 5 then
                                        local name = sampGetPlayerNickname(i)
                                        if name and name ~= '' then table.insert(candidates, { id = i, name = name }) end
                                    end
                                end
                            end

							if #candidates == 0 then
								local msg = u8:decode(u8'играков с 1-5 уровнем нет')
								if type(sampAddChatMessage) == 'function' then sampAddChatMessage(msg, -1) end
								isRunning = false
								break
							end

                            local idx = 1
                            while idx <= #candidates do
                                local p = candidates[idx]
								if not isRunning or searchMode ~= 'serch' then break end
								-- дождаться закрытия окна решения, если открыто
								while DecisionOpen[0] do wait(50) end
                                -- удалить из очереди тех, кто вышел с сервера; новых не добавляем
                                if not sampIsPlayerConnected(p.id) then
                                    table.remove(candidates, idx)
                                    goto next_candidate
                                end
								-- выполнить /re на игрока
								local nowMs = os.clock() * 1000
								if (nowMs - lastCommandTime) >= commandCooldown then
									sampSendChat(string.format('/re %s', p.name))
									lastCommandTime = nowMs
									reCommandTime = os.clock()
								end
								currentSearchTargetId = p.id
                                -- пауза 7 секунд между проверками
                                local untilTime = os.clock() + 7.0
								while os.clock() < untilTime do
									if not isRunning or searchMode ~= 'serch' then break end
									wait(50)
								end
								-- если окно решения открылось (обнаружение), ждать закрытия
								if DecisionOpen[0] then
									while DecisionOpen[0] and isRunning and searchMode == 'serch' do wait(50) end
								end
                                -- если произошёл бан, небольшая пауза 1с перед следующим
                                if banOccurredFlag then
                                    banOccurredFlag = false
                                    local untilOff = os.clock() + 1.0
                                    while os.clock() < untilOff do
                                        if not isRunning or searchMode ~= 'serch' then break end
                                        wait(50)
                                    end
                                end
                                idx = idx + 1
                                ::next_candidate::
                            end
							-- цикл: пересобрать список заново
						end
					end)
				end
			end
		else
			isRunning = false
			addNotification(u8'Закончил работу')
			suppressServerMessages = false
		end
	end
	imgui.PopStyleColor(3)
	
	imgui.Dummy(imgui.ImVec2(0, 6))
	


	imgui.Text(u8'Команда для бана бота')
	imgui.PushItemWidth(-1)
	local changed = imgui.InputText(u8'##ban_msg', banMessage, ffi.sizeof(banMessage))
	if changed then saveSettings() end
	imgui.PopItemWidth()
	imgui.Text(u8'Тег: {BotName} будет заменён на ник цели')
	
imgui.Dummy(imgui.ImVec2(0, 8))
imgui.Separator()
imgui.Dummy(imgui.ImVec2(0, 6))

-- Режим поиска ботов
imgui.Text(u8'Режим поиска ботов:')
imgui.Dummy(imgui.ImVec2(0, 4))
do
    local modeAvailW = imgui.GetContentRegionAvail().x
    local modeBtnW = (modeAvailW - 8.0) / 2
    if searchMode == 'idle' then
        imgui.PushStyleColor(imgui.Col.Button, imgui.ImVec4(0.50, 0.28, 0.88, 0.90))
        imgui.PushStyleColor(imgui.Col.ButtonHovered, imgui.ImVec4(0.60, 0.35, 0.98, 0.95))
        imgui.PushStyleColor(imgui.Col.ButtonActive, imgui.ImVec4(0.70, 0.42, 1.00, 1.00))
        imgui.Button(u8'Idle', imgui.ImVec2(modeBtnW, 30))
        if imgui.IsItemHovered() then
            imgui.BeginTooltip()
            imgui.Text(u8'Стандартный режим')
            imgui.Text(u8'Сканирует всех в зоне стрима')
            imgui.Text(u8'и срабатывает по признакам бота')
            imgui.EndTooltip()
        end
        imgui.PopStyleColor(3)
    else
        if SecondaryButton(u8'Idle', imgui.ImVec2(modeBtnW, 30)) then searchMode = 'idle'; saveSettings() end
        if imgui.IsItemHovered() then
            imgui.BeginTooltip()
            imgui.Text(u8'Стандартный режим')
            imgui.Text(u8'Сканирует всех в зоне стрима')
            imgui.Text(u8'и срабатывает по признакам бота')
            imgui.EndTooltip()
        end
    end
    imgui.SameLine()
    if searchMode == 'serch' then
        imgui.PushStyleColor(imgui.Col.Button, imgui.ImVec4(0.50, 0.28, 0.88, 0.90))
        imgui.PushStyleColor(imgui.Col.ButtonHovered, imgui.ImVec4(0.60, 0.35, 0.98, 0.95))
        imgui.PushStyleColor(imgui.Col.ButtonActive, imgui.ImVec4(0.70, 0.42, 1.00, 1.00))
        imgui.Button(u8'Serch', imgui.ImVec2(modeBtnW, 30))
        if imgui.IsItemHovered() then
            imgui.BeginTooltip()
            imgui.Text(u8'Последовательная проверка')
            imgui.Text(u8'По очереди делает /re на игроков 1–5 уровня')
            imgui.Text(u8'Анализирует только текущую цель слежки')
            imgui.EndTooltip()
        end
        imgui.PopStyleColor(3)
    else
        if SecondaryButton(u8'Serch', imgui.ImVec2(modeBtnW, 30)) then searchMode = 'serch'; saveSettings() end
        if imgui.IsItemHovered() then
            imgui.BeginTooltip()
            imgui.Text(u8'Последовательная проверка')
            imgui.Text(u8'По очереди делает /re на игроков 1–5 уровня')
            imgui.Text(u8'Анализирует только текущую цель слежки')
            imgui.EndTooltip()
        end
    end
end

imgui.Dummy(imgui.ImVec2(0, 8))
imgui.Separator()
imgui.Dummy(imgui.ImVec2(0, 6))
	
	imgui.Text(u8'Горячие клавиши:')
	imgui.Dummy(imgui.ImVec2(0, 4))

	local availWidth = imgui.GetContentRegionAvail().x
	local labelWidth = 160.0
	local valueWidth = 80.0
	local changeBtnWidth = 100.0
	local changeBtnX = labelWidth + valueWidth + 12

	imgui.Text(u8'Клавиша "Забанить":')
	imgui.SameLine(labelWidth)
	local keyName = vkeys.id_to_name(banKey[0]) or string.format("0x%02X", banKey[0])
	imgui.Text(keyName)
	imgui.SameLine(changeBtnX)
	if waitingForBanKey then
		imgui.TextColored(imgui.ImVec4(1.0, 0.5, 0.0, 1.0), u8'Нажмите...')
	else
		if SecondaryButton(u8'Изменить##ban_key', imgui.ImVec2(changeBtnWidth, 28)) then
			waitingForBanKey = true
		end
	end

	imgui.Text(u8'Клавиша "Пропустить":')
	imgui.SameLine(labelWidth)
	local skipKeyName = vkeys.id_to_name(skipKey[0]) or string.format("0x%02X", skipKey[0])
	imgui.Text(skipKeyName)
	imgui.SameLine(changeBtnX)
	if waitingForSkipKey then
		imgui.TextColored(imgui.ImVec4(1.0, 0.5, 0.0, 1.0), u8'Нажмите...')
	else
		if SecondaryButton(u8'Изменить##skip_key', imgui.ImVec2(changeBtnWidth, 28)) then
			waitingForSkipKey = true
		end
	end
	
	imgui.Dummy(imgui.ImVec2(0, 8))
	imgui.Separator()
	imgui.Dummy(imgui.ImVec2(0, 6))

-- Фоновый режим и клавиша активации
imgui.Text(u8'Фоновый режим:')
imgui.SameLine()
local bgEnabled = backgroundMode[0]
if imgui.Checkbox(u8'##bg_mode', backgroundMode) then
    saveSettings()
end
if imgui.IsItemHovered() then
    imgui.BeginTooltip()
    imgui.Text(u8'Фоновый режим, проверяет ботов без /re и окна')
    imgui.Text(u8'После предлогает уйти за ним в слежку, если подозрения подтверждаются')
    imgui.EndTooltip()
end

imgui.Dummy(imgui.ImVec2(0, 4))
imgui.Text(u8'Клавиша активации:')
imgui.SameLine(160.0)
local actKeyName = vkeys.id_to_name(activationKey[0]) or string.format("0x%02X", activationKey[0])
imgui.Text(actKeyName)
imgui.SameLine(160.0 + 80.0 + 12)
if waitingForActivationKey then
    imgui.TextColored(imgui.ImVec4(1.0, 0.5, 0.0, 1.0), u8'Нажмите...')
else
    if SecondaryButton(u8'Изменить##act_key', imgui.ImVec2(100.0, 28)) then
        waitingForActivationKey = true
    end
end

	-- Разделитель между фоновым режимом и режимом бана
	imgui.Dummy(imgui.ImVec2(0, 8))
	imgui.Separator()
	imgui.Dummy(imgui.ImVec2(0, 6))
	imgui.Text(u8'Режим бана:')
	imgui.Dummy(imgui.ImVec2(0, 4))
	
	local availWidth2 = imgui.GetContentRegionAvail().x
	local buttonSpacing2 = 8.0
	local banModeButtonWidth = (availWidth2 - buttonSpacing2) / 2

	if isAutoBan[0] then

		local activeColor = imgui.ImVec4(0.50, 0.28, 0.88, 0.90)
		local hoverColor = imgui.ImVec4(0.60, 0.35, 0.98, 0.95)
		local pressedColor = imgui.ImVec4(0.70, 0.42, 1.00, 1.00)
		imgui.PushStyleColor(imgui.Col.Button, activeColor)
		imgui.PushStyleColor(imgui.Col.ButtonHovered, hoverColor)
		imgui.PushStyleColor(imgui.Col.ButtonActive, pressedColor)
		if imgui.Button(u8'Auto Ban', imgui.ImVec2(banModeButtonWidth, 32)) then
			isAutoBan[0] = true
			saveSettings()
		end
		imgui.PopStyleColor(3)
		if imgui.IsItemHovered() then
			imgui.BeginTooltip()
			imgui.Text(u8'Автоматический режим бана')
			imgui.Text(u8'После окончания обратного отсчета')
			imgui.Text(u8'бан выполняется автоматически')
			imgui.EndTooltip()
		end
	else

		if SecondaryButton(u8'Auto Ban', imgui.ImVec2(banModeButtonWidth, 32)) then
			isAutoBan[0] = true
			saveSettings()
		end
		if imgui.IsItemHovered() then
			imgui.BeginTooltip()
			imgui.Text(u8'Автоматический режим бана')
			imgui.Text(u8'После окончания обратного отсчета')
			imgui.Text(u8'бан выполняется автоматически')
			imgui.EndTooltip()
		end
	end
	
	imgui.SameLine()

	if not isAutoBan[0] then

		local activeColor = imgui.ImVec4(0.50, 0.28, 0.88, 0.90)
		local hoverColor = imgui.ImVec4(0.60, 0.35, 0.98, 0.95)
		local pressedColor = imgui.ImVec4(0.70, 0.42, 1.00, 1.00)
		imgui.PushStyleColor(imgui.Col.Button, activeColor)
		imgui.PushStyleColor(imgui.Col.ButtonHovered, hoverColor)
		imgui.PushStyleColor(imgui.Col.ButtonActive, pressedColor)
		if imgui.Button(u8'Manual Ban (Рекамендуется)', imgui.ImVec2(banModeButtonWidth, 32)) then
			isAutoBan[0] = false
			saveSettings()
		end
		imgui.PopStyleColor(3)
		if imgui.IsItemHovered() then
			imgui.BeginTooltip()
			imgui.Text(u8'Ручной режим бана')
			imgui.Text(u8'После окончания обратного отсчета')
			imgui.Text(u8'требуется нажатие кнопки или клавиши')
			imgui.EndTooltip()
		end
	else

		if SecondaryButton(u8'Manual Ban (Рекамендуется)', imgui.ImVec2(banModeButtonWidth, 32)) then
			isAutoBan[0] = false
			saveSettings()
		end
		if imgui.IsItemHovered() then
			imgui.BeginTooltip()
			imgui.Text(u8'Ручной режим бана')
			imgui.Text(u8'После окончания обратного отсчета')
			imgui.Text(u8'требуется нажатие кнопки или клавиши')
			imgui.EndTooltip()
		end
	end
	
	imgui.Dummy(imgui.ImVec2(0, 8))
	imgui.Separator()
	imgui.Dummy(imgui.ImVec2(0, 6))

	imgui.AlignTextToFramePadding()
	imgui.Text(u8'Задержка обратного отсчета:')
	imgui.SameLine()
	imgui.PushItemWidth(120)

	local prevValueBeforeCheck = banCountdownMs[0]
	local countdownChanged = imgui.InputInt(u8'##ban_countdown_ms', banCountdownMs)
	if countdownChanged then

		if banCountdownMs[0] > 60000 then banCountdownMs[0] = 60000 end

		if banCountdownMs[0] < 3000 then

			if prevValueBeforeCheck >= 3000 or not lowDelayConfirmed then


				lowDelayWarningState[0] = true
				lowDelayContinueEnabled = false
				lowDelayContinueEnableTime = os.clock() + 5.0

				lowDelayPrevValue = prevValueBeforeCheck
			else

				lowDelayPrevValue = banCountdownMs[0]
				saveSettings()
			end
		else

			lowDelayPrevValue = banCountdownMs[0]
			lowDelayConfirmed = false
			saveSettings()
		end
	end
	imgui.PopItemWidth()

	if imgui.IsItemHovered() then

		local itemMin = imgui.GetItemRectMin()
		local itemMax = imgui.GetItemRectMax()
		local mousePos = imgui.GetMousePos()


		local itemWidth = itemMax.x - itemMin.x
		local mouseOffsetX = mousePos.x - itemMin.x

		if mouseOffsetX < itemWidth * 0.7 then
			imgui.BeginTooltip()
			imgui.Text(u8'Время обратного отсчета перед возможностью')
			imgui.Text(u8'выполнить бан (1 секунда = 1000мс)')
			imgui.EndTooltip()
		end
	end

    imgui.EndChild()

    imgui.Dummy(imgui.ImVec2(0, 0))
    local bottomBtnWidth = imgui.GetContentRegionAvail().x
    local bottomBtnHeight = 32.0
    if SecondaryButton(u8'Логер банов', imgui.ImVec2(bottomBtnWidth, bottomBtnHeight)) then
		WinState[0] = false
		BanLoggerState[0] = true
	end
	if updateAvailableVersion then
		imgui.Dummy(imgui.ImVec2(0, 6))
		local label = string.format(u8'Обновление v%s', updateAvailableVersion)
		if SecondaryButton(label, imgui.ImVec2(bottomBtnWidth, bottomBtnHeight)) then
			UpdateWindowState[0] = true
		end
	end

		imgui.EndChild()
		imgui.SameLine()

		imgui.BeginChild('##col_right', imgui.ImVec2(leftColWidth, columnsHeight), false, imgui.WindowFlags.NoScrollbar)
			local ravail = imgui.GetContentRegionAvail()
			imgui.SetCursorPosX(imgui.GetCursorPosX() + sidePadding)
			imgui.BeginChild('##card_right', imgui.ImVec2(ravail.x - sidePadding * 2, 0), true, imgui.WindowFlags.NoScrollbar)
				local contentAvail = imgui.GetContentRegionAvail()
				local bottomButtonWidth = 280.0
				local bottomButtonHeight = 32.0
				local reservedBottom = bottomButtonHeight + 16.0
				local listHeight = contentAvail.y - reservedBottom
				if listHeight < 80.0 then listHeight = contentAvail.y - bottomButtonHeight end

				imgui.BeginChild('##card_right_list', imgui.ImVec2(0, listHeight), false, imgui.WindowFlags.NoScrollbar)

					local header = u8'Список координат'
					local availX = imgui.GetContentRegionAvail().x
					local textW = imgui.CalcTextSize(header).x
					local baseX = imgui.GetCursorPosX()
					imgui.SetCursorPosX(baseX + math.max(0, (availX - textW) * 0.5))
					imgui.Text(header)
					imgui.Dummy(imgui.ImVec2(0, 6))
					local toDeleteIndex = nil
					for i, coord in ipairs(teleportCoords) do
						if not teleportNames[i] then
							teleportNames[i] = new.char[64](u8(string.format('Точка %d', i)))
						end
						imgui.Text(u8(string.format('Коорд. #%d: (%.2f, %.2f, %.2f)', i, coord.x, coord.y, coord.z)))

						local rowAvail = imgui.GetContentRegionAvail().x
						local delBtnW = 110.0
						local spacing = 8.0
						local inputWidth = math.max(100.0, rowAvail - delBtnW - spacing)

						imgui.PushItemWidth(inputWidth)
						local changedName = imgui.InputText(u8(string.format('##tp_name_%d', i)), teleportNames[i], ffi.sizeof(teleportNames[i]))
						if changedName then saveCoords() end
						imgui.PopItemWidth()

						local deleteBtnX = rowAvail - delBtnW
						imgui.SameLine(deleteBtnX)
						if DangerButton(u8'Удалить##del_' .. i, imgui.ImVec2(delBtnW, 28)) then
							toDeleteIndex = i
						end
						
						imgui.Dummy(imgui.ImVec2(0, 4))
						if i < #teleportCoords then imgui.Separator() imgui.Dummy(imgui.ImVec2(0, 4)) end
					end

					if toDeleteIndex ~= nil then
						table.remove(teleportCoords, toDeleteIndex)
						table.remove(teleportNames, toDeleteIndex)
						if #teleportCoords == 0 then
							teleportIndex = 1
						else
							if teleportIndex > #teleportCoords then teleportIndex = #teleportCoords end
							if teleportIndex < 1 then teleportIndex = 1 end
						end
						saveCoords()
					end
				imgui.EndChild()

				imgui.Dummy(imgui.ImVec2(0, 8))
				local availX2 = imgui.GetContentRegionAvail().x
				local baseX2 = imgui.GetCursorPosX()
				imgui.SetCursorPosX(baseX2 + math.max(0, (availX2 - bottomButtonWidth) * 0.5))
				if SecondaryButton(u8'Добавить текущие координаты', imgui.ImVec2(bottomButtonWidth, bottomButtonHeight)) then
					local px, py, pz = getCharCoordinates(PLAYER_PED)
					table.insert(teleportCoords, { x = px, y = py, z = pz })
					teleportNames[#teleportCoords] = new.char[64](u8(string.format('Точка %d', #teleportCoords)))
					saveCoords()
				end
			imgui.EndChild()
		imgui.EndChild()

		imgui.Dummy(imgui.ImVec2(0, 12))
		imgui.Separator()
		imgui.Dummy(imgui.ImVec2(0, 8))
		
		local mainAvailWidth = imgui.GetContentRegionAvail().x
		local socialBtnHeight = 36.0
		local socialBtnSpacing = 8.0

		local socialBtnWidth = (mainAvailWidth - socialBtnSpacing * 2) / 3

		if SecondaryButton(u8'VKontakte', imgui.ImVec2(socialBtnWidth, socialBtnHeight)) then
			openUrl('https://vk.com/id855134297')
		end
		imgui.SameLine(0, socialBtnSpacing)

		if SecondaryButton(u8'Telegram', imgui.ImVec2(socialBtnWidth, socialBtnHeight)) then
			openUrl('https://t.me/NehtoOtto')
		end
		imgui.SameLine(0, socialBtnSpacing)

		if SecondaryButton(u8'Discord', imgui.ImVec2(socialBtnWidth, socialBtnHeight)) then
			openUrl('https://discordapp.com/users/1171154160998174741')
		end

		imgui.PopStyleColor(6)
	    end

		if not showWelcomeAnimation then

			local currentTime = os.clock()
			local elapsed = currentTime - welcomeAnimationStartTime
			local fadeInDuration = 0.5
			local showDuration = 6.0
			local fadeOutDuration = 0.5
			local totalDuration = fadeInDuration + showDuration + fadeOutDuration
			
			local alpha = 1.0
			if elapsed < fadeInDuration then

				alpha = elapsed / fadeInDuration
			elseif elapsed < fadeInDuration + showDuration then

				alpha = 1.0
			elseif elapsed < totalDuration then

				alpha = 1.0 - ((elapsed - fadeInDuration - showDuration) / fadeOutDuration)
			else

				alpha = 0.0
				showWelcomeAnimation = true
				welcomeAnimationJustCompleted = true
				saveSettings()
				welcomeAnimationStartTime = 0
			end
			
			if alpha > 0 then

				local drawList = imgui.GetWindowDrawList()
				local windowPos = imgui.GetWindowPos()
				local windowSize = imgui.GetWindowSize()

				local style = imgui.GetStyle()
				local windowBg = style.Colors[imgui.Col.WindowBg]

				local bgColor = imgui.GetColorU32Vec4(imgui.ImVec4(
					windowBg.x, 
					windowBg.y, 
					windowBg.z, 
					windowBg.w * alpha
				))
				drawList:AddRectFilled(
					windowPos, 
					imgui.ImVec2(windowPos.x + windowSize.x, windowPos.y + windowSize.y),
					bgColor
				)

				local text1 = u8'Привет, я Bbot!'

				imgui.SetWindowFontScale(2.5)
				local text1Size = imgui.CalcTextSize(text1)

				local text2 = u8'Меня создали для помощи администрации, давай побаним ботов?'
				imgui.SetWindowFontScale(1.25)
				local text2Size = imgui.CalcTextSize(text2)
				imgui.SetWindowFontScale(1.0)

				local totalHeight = text1Size.y + text2Size.y + 30

				local centerX = windowPos.x + windowSize.x / 2
				local centerY = windowPos.y + windowSize.y / 2
				local text1Y = centerY - totalHeight / 2
				local text1X = centerX - text1Size.x / 2

				local textAlpha = alpha

				local textColor = imgui.GetColorU32Vec4(imgui.ImVec4(1.0, 1.0, 1.0, textAlpha))



				imgui.SetWindowFontScale(2.5)
				drawList:AddText(imgui.ImVec2(text1X, text1Y), textColor, text1)
				imgui.SetWindowFontScale(1.0)

				local text2Y = text1Y + text1Size.y + 30
				local text2X = centerX - text2Size.x / 2
				imgui.SetWindowFontScale(1.25)
				drawList:AddText(imgui.ImVec2(text2X, text2Y), textColor, text2)
				imgui.SetWindowFontScale(1.0)
			end
		end

		if showWelcomeAnimation and returnAnimationStartTime > 0 and not returnAnimationShown then

			local currentTime = os.clock()
			local elapsed = currentTime - returnAnimationStartTime
			local fadeInDuration = 0.5
			local showDuration = 1.5
			local fadeOutDuration = 0.5
			local totalDuration = fadeInDuration + showDuration + fadeOutDuration
			
			local alpha = 1.0
			if elapsed < fadeInDuration then

				alpha = elapsed / fadeInDuration
			elseif elapsed < fadeInDuration + showDuration then

				alpha = 1.0
			elseif elapsed < totalDuration then

				alpha = 1.0 - ((elapsed - fadeInDuration - showDuration) / fadeOutDuration)
			else

				alpha = 0.0
				returnAnimationShown = true
				returnAnimationStartTime = 0
			end
			
			if alpha > 0 then

				local drawList = imgui.GetWindowDrawList()
				local windowPos = imgui.GetWindowPos()
				local windowSize = imgui.GetWindowSize()

				local style = imgui.GetStyle()
				local windowBg = style.Colors[imgui.Col.WindowBg]

				local bgColor = imgui.GetColorU32Vec4(imgui.ImVec4(
					windowBg.x, 
					windowBg.y, 
					windowBg.z, 
					windowBg.w * alpha
				))
				drawList:AddRectFilled(
					windowPos, 
					imgui.ImVec2(windowPos.x + windowSize.x, windowPos.y + windowSize.y),
					bgColor
				)

				local text1 = u8'С возвращением'

				imgui.SetWindowFontScale(2.5)
				local text1Size = imgui.CalcTextSize(text1)

				local text2 = u8'Побаним ботов вместе!'
				imgui.SetWindowFontScale(1.25)
				local text2Size = imgui.CalcTextSize(text2)
				imgui.SetWindowFontScale(1.0)

				local totalHeight = text1Size.y + text2Size.y + 30

				local centerX = windowPos.x + windowSize.x / 2
				local centerY = windowPos.y + windowSize.y / 2
				local text1Y = centerY - totalHeight / 2
				local text1X = centerX - text1Size.x / 2

				local textAlpha = alpha

				local textColor = imgui.GetColorU32Vec4(imgui.ImVec4(1.0, 1.0, 1.0, textAlpha))
				
				imgui.SetWindowFontScale(2.5)
				drawList:AddText(imgui.ImVec2(text1X, text1Y), textColor, text1)
				imgui.SetWindowFontScale(1.0)

				local text2Y = text1Y + text1Size.y + 30
				local text2X = centerX - text2Size.x / 2
				imgui.SetWindowFontScale(1.25)
				drawList:AddText(imgui.ImVec2(text2X, text2Y), textColor, text2)
				imgui.SetWindowFontScale(1.0)
			end
		end
		
		imgui.End()
end)

imgui.OnFrame(function() return isRunning end, function(player)

	QuickTPState[0] = true
	imgui.SetNextWindowPos(imgui.ImVec2(20, 220), imgui.Cond.FirstUseEver, imgui.ImVec2(0.0, 0.0))

	local interactiveUiOpen = (WinState and WinState[0]) or (DecisionOpen and DecisionOpen[0])
	local quickFlags = imgui.WindowFlags.AlwaysAutoResize + imgui.WindowFlags.NoCollapse
	imgui.Begin(u8'BBot — Телепорты', QuickTPState, quickFlags)
		imgui.Text(u8'Быстрый телепорт')
		imgui.Dummy(imgui.ImVec2(0, 6))
		if #teleportCoords == 0 then
			imgui.Text(u8'Нет координат')
		else
			local btnWidth = 220.0
			for i, coord in ipairs(teleportCoords) do
				local nameStr = teleportNames[i] and ffi.string(teleportNames[i]) or string.format('Точка %d', i)

				if imgui.Button(nameStr, imgui.ImVec2(btnWidth, 30)) then

					local currentTime = os.clock() * 1000
					if (currentTime - lastCommandTime) >= commandCooldown then
						sampSendChat(string.format("/gc %.2f %.2f %.2f 0 0", coord.x, coord.y, coord.z))
						lastCommandTime = currentTime


					local notificationText = string.format(u8'Телепортировался к %s', nameStr)
					addNotification(notificationText)
					end
				end
				imgui.Dummy(imgui.ImVec2(0, 4))
			end
		end
	imgui.End()
end).HideCursor = function()

	return not ((WinState and WinState[0]) or (DecisionOpen and DecisionOpen[0]))
end

imgui.OnFrame(function() return DecisionOpen[0] end, function(player)
	if not themeApplied then
		applyUiTheme()
		themeApplied = true
	end

	imgui.SetNextWindowPos(imgui.ImVec2(600,400), imgui.Cond.FirstUseEver, imgui.ImVec2(0.5, 0.5))
    imgui.SetNextWindowSize(imgui.ImVec2(450, 300), imgui.Cond.Always)
	imgui.Begin(u8'BBot — Решение', DecisionOpen, imgui.WindowFlags.NoResize + imgui.WindowFlags.NoCollapse)

	imgui.BeginChild('##card_decision', imgui.ImVec2(0, 0), true, imgui.WindowFlags.NoScrollbar)
	if pendingReport ~= nil then
		imgui.Separator()
		imgui.Dummy(imgui.ImVec2(0, 8))

		imgui.Text(u8'ID игрока:')
		imgui.SameLine()
		imgui.PushStyleColor(imgui.Col.Text, imgui.ImVec4(0.50, 0.28, 0.88, 1.00))
		imgui.Text(u8(string.format("%d", pendingReport.id)))
		imgui.PopStyleColor()
		
		imgui.Text(u8'Имя:')
		imgui.SameLine()
		imgui.PushStyleColor(imgui.Col.Text, imgui.ImVec4(0.50, 0.28, 0.88, 1.00))
		imgui.Text(u8(pendingReport.name))
		imgui.PopStyleColor()
		
		imgui.Text(u8'Уровень:')
		imgui.SameLine()
		imgui.PushStyleColor(imgui.Col.Text, imgui.ImVec4(0.50, 0.28, 0.88, 1.00))
		imgui.Text(u8(string.format("%d", pendingReport.level)))
		imgui.PopStyleColor()
		
		imgui.Text(u8'Расстояние:')
		imgui.SameLine()
		imgui.PushStyleColor(imgui.Col.Text, imgui.ImVec4(0.50, 0.28, 0.88, 1.00))
		imgui.Text(u8(string.format("%.1fм", pendingReport.distance)))
		imgui.PopStyleColor()
		
		imgui.Dummy(imgui.ImVec2(0, 12))
		imgui.Separator()
		imgui.Dummy(imgui.ImVec2(0, 12))

		local availWidth = imgui.GetContentRegionAvail().x
		local buttonSpacing = 12.0
		local buttonWidth = (availWidth - buttonSpacing) / 2
		local buttonHeight = 32.0

		local currentTime = os.clock()
		local elapsedTime = currentTime - banCountdownStartTime
		local countdownDuration = banCountdownMs[0] / 1000.0
		local remainingTime = countdownDuration - elapsedTime
		local isCountdownActive = remainingTime > 0

		if not isCountdownActive and isAutoBan[0] and pendingReport and not autoBanTriggered then

			autoBanTriggered = true
			performBan()
		end
		
		local banKeyName = vkeys.id_to_name(banKey[0]) or string.format("0x%02X", banKey[0])
		local banButtonLabel = ""
		if isCountdownActive then

			banButtonLabel = u8(string.format('Забанить (%.3fс)', remainingTime))
		else
			banButtonLabel = u8('Забанить (' .. banKeyName .. ')')
		end

		local banButtonClicked = false
		if isCountdownActive then

			imgui.PushStyleColor(imgui.Col.Button, imgui.ImVec4(0.40, 0.40, 0.42, 0.60))
			imgui.PushStyleColor(imgui.Col.ButtonHovered, imgui.ImVec4(0.40, 0.40, 0.42, 0.60))
			imgui.PushStyleColor(imgui.Col.ButtonActive, imgui.ImVec4(0.40, 0.40, 0.42, 0.60))
			imgui.Button(banButtonLabel, imgui.ImVec2(buttonWidth, buttonHeight))
			imgui.PopStyleColor(3)
		else

			local baseColor = imgui.ImVec4(0.85, 0.20, 0.22, 0.90)
			local hoverColor = imgui.ImVec4(0.95, 0.28, 0.30, 0.95)
			local activeColor = imgui.ImVec4(1.00, 0.35, 0.38, 1.00)
			imgui.PushStyleColor(imgui.Col.Button, baseColor)
			imgui.PushStyleColor(imgui.Col.ButtonHovered, hoverColor)
			imgui.PushStyleColor(imgui.Col.ButtonActive, activeColor)
			banButtonClicked = imgui.Button(banButtonLabel, imgui.ImVec2(buttonWidth, buttonHeight))
			imgui.PopStyleColor(3)
		end
		
		if banButtonClicked and not isCountdownActive then

			performBan()
		end
		imgui.SameLine()
		local skipKeyName = vkeys.id_to_name(skipKey[0]) or string.format("0x%02X", skipKey[0])
		if SecondaryButton(u8('Пропустить (' .. skipKeyName .. ')'), imgui.ImVec2(buttonWidth, buttonHeight)) then
			sampSendChat("/reoff")
			if pendingReport and pendingReport.name then
				skippedPlayers[pendingReport.name] = true
			end
			DecisionOpen[0] = false
			pendingReport = nil
			lastDecisionCloseTime = os.clock() * 1000
		end
	else
		imgui.Text(u8'Нет данных')
		if SecondaryButton(u8'Закрыть', imgui.ImVec2(120, 30)) then
			DecisionOpen[0] = false
			lastDecisionCloseTime = os.clock() * 1000
		end
	end
	imgui.EndChild()
	imgui.End()
end)

imgui.OnFrame(function() return lowDelayWarningState[0] end, function()

	local screenWidth, screenHeight = getScreenResolution()
	local windowWidth = 500.0
	local windowHeight = 280.0

	imgui.SetNextWindowPos(imgui.ImVec2(screenWidth / 2, screenHeight / 2), imgui.Cond.Always, imgui.ImVec2(0.5, 0.5))
	imgui.SetNextWindowSize(imgui.ImVec2(windowWidth, windowHeight), imgui.Cond.Always)


	local windowFlags = imgui.WindowFlags.NoResize + imgui.WindowFlags.NoCollapse + imgui.WindowFlags.NoMove
	
	imgui.Begin(u8'Предупреждение', lowDelayWarningState, windowFlags)

	if not lowDelayWarningState[0] then
		lowDelayWarningState[0] = true
	end

	local currentTime = os.clock()
	if currentTime >= lowDelayContinueEnableTime then
		lowDelayContinueEnabled = true
	end

	imgui.Dummy(imgui.ImVec2(0, 10))
	imgui.Text(u8'Не рекомендуется ставить задержку менее 3000мс')
	imgui.Dummy(imgui.ImVec2(0, 8))
	imgui.Text(u8'Это может вызвать проблемы с работой BBot,')
	imgui.Text(u8'а так же могут появиться ошибочные блокировки!')
	
	imgui.Dummy(imgui.ImVec2(0, 20))

	local availWidth = imgui.GetContentRegionAvail().x
	local buttonSpacing = 12.0
	local buttonWidth = (availWidth - buttonSpacing) / 2
	local buttonHeight = 35.0

	if SecondaryButton(u8'Отказаться', imgui.ImVec2(buttonWidth, buttonHeight)) then

		if lowDelayPrevValue >= 3000 then
			banCountdownMs[0] = lowDelayPrevValue
		else
			banCountdownMs[0] = 3000
		end
		lowDelayWarningState[0] = false
		saveSettings()
	end
	
	imgui.SameLine()

	if not lowDelayContinueEnabled then

		local remainingTime = lowDelayContinueEnableTime - currentTime
		if remainingTime < 0 then remainingTime = 0 end
		local remainingSeconds = math.ceil(remainingTime)
		local buttonLabel = u8(string.format('Продолжить (%dс)', remainingSeconds))

		imgui.PushStyleColor(imgui.Col.Button, imgui.ImVec4(0.40, 0.40, 0.42, 0.60))
		imgui.PushStyleColor(imgui.Col.ButtonHovered, imgui.ImVec4(0.40, 0.40, 0.42, 0.60))
		imgui.PushStyleColor(imgui.Col.ButtonActive, imgui.ImVec4(0.40, 0.40, 0.42, 0.60))
		imgui.Button(buttonLabel, imgui.ImVec2(buttonWidth, buttonHeight))
		imgui.PopStyleColor(3)
	else

		if imgui.Button(u8'Продолжить', imgui.ImVec2(buttonWidth, buttonHeight)) then

			lowDelayConfirmed = true
			lowDelayWarningState[0] = false
			saveSettings()
		end
	end
	
	imgui.End()
end)

local prevWinState = false
imgui.OnFrame(function() return true end, function()

	if prevBanLoggerState and not BanLoggerState[0] then

		WinState[0] = true
	end

	if prevWinState and not WinState[0] then

		welcomeAnimationJustCompleted = false
	end

	prevBanLoggerState = BanLoggerState[0]
	prevWinState = WinState[0]
end).HideCursor = function()

	return true
end

imgui.OnFrame(function() return BanLoggerState[0] end, function(player)
	if not themeApplied then
		applyUiTheme()
		themeApplied = true
	end
	imgui.SetNextWindowPos(imgui.ImVec2(500, 200), imgui.Cond.FirstUseEver, imgui.ImVec2(0.5, 0.5))
	imgui.SetNextWindowSize(imgui.ImVec2(800, 650), imgui.Cond.Always)
	imgui.Begin(u8'Логер банов', BanLoggerState, imgui.WindowFlags.NoResize + imgui.WindowFlags.NoCollapse)

	local bans = loadBans()
	local groupedBans = groupBansByDate(bans)
	
	-- Поиск по нику (по центру, без надписи)
	imgui.Dummy(imgui.ImVec2(0, 4))
	local searchWidth = 300.0
	local availW = imgui.GetContentRegionAvail().x
	local baseX = imgui.GetCursorPosX()
	local offsetX = math.max(0, (availW - searchWidth) * 0.5)
	imgui.SetCursorPosX(baseX + offsetX)
	imgui.PushItemWidth(searchWidth)
	imgui.InputText('##ban_search', banSearchBuf, ffi.sizeof(banSearchBuf))
	-- Placeholder внутри поля, когда пусто
	local _searchStrForPlaceholder = ffi.string(banSearchBuf)
	if not _searchStrForPlaceholder or _searchStrForPlaceholder == '' then
		local style = imgui.GetStyle()
		local pad = style.FramePadding
		local minRect = imgui.GetItemRectMin()
		local drawList = imgui.GetWindowDrawList()
		local textPos = imgui.ImVec2(minRect.x + pad.x, minRect.y + pad.y)
		local disabledCol = imgui.GetColorU32Vec4(style.Colors[imgui.Col.TextDisabled])
		drawList:AddText(textPos, disabledCol, u8'Найти...')
	end
	imgui.PopItemWidth()
	local searchStr = ffi.string(banSearchBuf)
	local hasFilter = searchStr ~= nil and searchStr ~= ''
	local searchLower = hasFilter and string.lower(searchStr) or ''

	if #groupedBans == 0 then
		imgui.Text(u8'Нет записей о банах')
	else

		imgui.BeginChild('##ban_list', imgui.ImVec2(0, 0), false, imgui.WindowFlags.NoScrollbar)
		local currentTime = os.clock()
		local copyAnimationDuration = 1.0
		
		for dateIdx, dateGroup in ipairs(groupedBans) do
			local date = dateGroup.date
			local dateBans = dateGroup.bans
			local count = #dateBans

			local formattedDate = formatDateToRussian(date)
			local banWord = getBanWord(count)
			local headerLabel = string.format("%s (%d %s)", formattedDate, count, banWord)

			-- Проверяем, есть ли совпадения в группе
			local groupHasMatch = false
			if hasFilter then
				for _, ban in ipairs(dateBans) do
					local nameLower = string.lower(ban.name or '')
					if string.find(nameLower, searchLower, 1, true) then
						groupHasMatch = true
						break
					end
				end
			else
				groupHasMatch = true
			end

			-- Если нет совпадений: показать затемнённый некликабельный заголовок, иначе обычный блок
			if hasFilter and not groupHasMatch then
				imgui.PushStyleColor(imgui.Col.Text, imgui.ImVec4(0.50, 0.50, 0.52, 0.58))
				imgui.Text(u8(headerLabel))
				imgui.PopStyleColor()
			else

			if imgui.CollapsingHeader(u8(headerLabel)) then
				dateExpandedStates[date] = true
				imgui.Indent(10.0)

				imgui.Text(u8'Ник Нэйм')
				imgui.SameLine(200)
				imgui.Text(u8'Дата и время')
				imgui.SameLine(400)
				imgui.Text(u8'Время слежки')
				imgui.Separator()

				for i, ban in ipairs(dateBans) do
					local isMatch = true
					if hasFilter then
						local nameLower = string.lower(ban.name or '')
						isMatch = string.find(nameLower, searchLower, 1, true) ~= nil
					end

					if not isMatch and hasFilter then
						imgui.PushStyleColor(imgui.Col.Text, imgui.ImVec4(0.50, 0.50, 0.52, 0.58))
						imgui.Text(u8(ban.name))
						imgui.PopStyleColor()
					else
						imgui.PushStyleColor(imgui.Col.Text, imgui.ImVec4(0.50, 0.28, 0.88, 1.00))
						imgui.Text(u8(ban.name))
						imgui.PopStyleColor()
					end
					
					imgui.SameLine(200)

					imgui.Text(u8(ban.timestamp))
					
					imgui.SameLine(400)

					if ban.timeDiff ~= "" then
						imgui.Text(u8(ban.timeDiff))
					else
						imgui.TextColored(imgui.ImVec4(0.5, 0.5, 0.5, 1.0), u8'—')
					end
					
					if i < #dateBans then
						imgui.Separator()
					end
				end

				imgui.Dummy(imgui.ImVec2(0, 8))
				local availWidth = imgui.GetContentRegionAvail().x
				local buttonWidth = 200.0
				local buttonX = (availWidth - buttonWidth) / 2
				if buttonX < 0 then buttonX = 0 end
				imgui.SetCursorPosX(imgui.GetCursorPosX() + buttonX)

				local buttonText = u8'Копировать список'
				local copyElapsed = copyButtonAnimationTime[date] and (currentTime - copyButtonAnimationTime[date]) or copyAnimationDuration
				if copyElapsed < copyAnimationDuration then

					buttonText = u8'Скопировано!'
					local animProgress = copyElapsed / copyAnimationDuration

					local greenIntensity = math.sin(animProgress * math.pi)
					local baseColor = imgui.ImVec4(0.22, 0.22, 0.26, 0.80)
					local greenTint = imgui.ImVec4(0.0, 0.8, 0.3, 0.0)
					local animColor = imgui.ImVec4(
						baseColor.x + greenTint.x * greenIntensity,
						baseColor.y + greenTint.y * greenIntensity,
						baseColor.z + greenTint.z * greenIntensity,
						baseColor.w
					)
					imgui.PushStyleColor(imgui.Col.Button, animColor)
					imgui.PushStyleColor(imgui.Col.ButtonHovered, imgui.ImVec4(
						animColor.x * 1.2, animColor.y * 1.2, animColor.z * 1.2, 0.90
					))
					imgui.PushStyleColor(imgui.Col.ButtonActive, imgui.ImVec4(
						animColor.x * 1.3, animColor.y * 1.3, animColor.z * 1.3, 1.00
					))
					imgui.Button(buttonText, imgui.ImVec2(buttonWidth, 32))
					imgui.PopStyleColor(3)
				else

					if SecondaryButton(buttonText, imgui.ImVec2(buttonWidth, 32)) then

						local nickList = {}
						for _, ban in ipairs(dateBans) do
							table.insert(nickList, ban.name)
						end
						local textToCopy = table.concat(nickList, '\n')
						if copyToClipboard(textToCopy) then

							copyButtonAnimationTime[date] = currentTime
							copyButtonClickedDate[date] = true

							addNotification(u8'Список скопирован')
						end
					end
				end
				
				imgui.Unindent(10.0)
			else
				dateExpandedStates[date] = false
			end

			end
			
			if dateIdx < #groupedBans then
				imgui.Dummy(imgui.ImVec2(0, 4))
			end
		end
		imgui.EndChild()
	end
	
	imgui.End()
end)

imgui.OnFrame(function() return reminderStartTime > 0 end, function()
	local currentTime = os.clock()
	local elapsed = currentTime - reminderStartTime
	local fadeInDuration = 0.5
	local showDuration = 4.0
	local fadeOutDuration = 0.5
	local totalDuration = fadeInDuration + showDuration + fadeOutDuration
	
	local alpha = 0.0
	if elapsed < fadeInDuration then

		alpha = elapsed / fadeInDuration
	elseif elapsed < fadeInDuration + showDuration then

		alpha = 1.0
	elseif elapsed < totalDuration then

		alpha = 1.0 - ((elapsed - fadeInDuration - showDuration) / fadeOutDuration)
	else

		alpha = 0.0
		reminderStartTime = 0
	end
	
	if alpha > 0 then

		local screenWidth, screenHeight = getScreenResolution()

		imgui.SetNextWindowPos(imgui.ImVec2(screenWidth / 2, screenHeight / 2), imgui.Cond.Always, imgui.ImVec2(0.5, 0.5))
		imgui.SetNextWindowSize(imgui.ImVec2(800, 250), imgui.Cond.Always)

		local windowFlags = imgui.WindowFlags.NoTitleBar + imgui.WindowFlags.NoResize + 
		                   imgui.WindowFlags.NoMove + imgui.WindowFlags.NoScrollbar +
		                   imgui.WindowFlags.NoInputs + imgui.WindowFlags.NoBackground
		
		ReminderState[0] = true
		imgui.Begin("##reminder", ReminderState, windowFlags)

		local drawList = imgui.GetWindowDrawList()
		local windowPos = imgui.GetWindowPos()
		local windowSize = imgui.GetWindowSize()

		local textPart1 = u8("Повышена активность ботов, ")
		local textPart2 = u8(tostring(reminderBotCount))
		local textPart3 = u8(" аккаунтов!")

		local fontSize = 1.75
		imgui.SetWindowFontScale(fontSize)
		local text1Size = imgui.CalcTextSize(textPart1)
		local text2Size = imgui.CalcTextSize(textPart2)
		local text3Size = imgui.CalcTextSize(textPart3)
		local totalTextWidth = text1Size.x + text2Size.x + text3Size.x
		local totalTextHeight = math.max(text1Size.y, math.max(text2Size.y, text3Size.y))
		imgui.SetWindowFontScale(1.0)

		local centerX = windowPos.x + windowSize.x / 2
		local centerY = windowPos.y + windowSize.y / 2
		local text1Y = centerY - totalTextHeight / 2
		local text1X = centerX - totalTextWidth / 2

		local darkPurpleColor = imgui.GetColorU32Vec4(imgui.ImVec4(0.4, 0.2, 0.6, alpha))

		local lightPurpleColor = imgui.GetColorU32Vec4(imgui.ImVec4(0.8, 0.6, 1.0, alpha))

		local shadowColor = imgui.GetColorU32Vec4(imgui.ImVec4(0.0, 0.0, 0.0, alpha * 0.8))

		local shadowOffset = 2
		
		imgui.SetWindowFontScale(fontSize)

		drawList:AddText(imgui.ImVec2(text1X + shadowOffset, text1Y + shadowOffset), shadowColor, textPart1)
		drawList:AddText(imgui.ImVec2(text1X, text1Y), darkPurpleColor, textPart1)

		local text2X = text1X + text1Size.x

		drawList:AddText(imgui.ImVec2(text2X + shadowOffset, text1Y + shadowOffset), shadowColor, textPart2)
		drawList:AddText(imgui.ImVec2(text2X, text1Y), lightPurpleColor, textPart2)

		local text3X = text2X + text2Size.x

		drawList:AddText(imgui.ImVec2(text3X + shadowOffset, text1Y + shadowOffset), shadowColor, textPart3)
		drawList:AddText(imgui.ImVec2(text3X, text1Y), darkPurpleColor, textPart3)
		
		imgui.SetWindowFontScale(1.0)
		
		imgui.End()
	end
end).HideCursor = function()
	return true
end

local NotificationWindowState = new.bool(true)
imgui.OnFrame(function() return #notifications > 0 end, function()

	local screenWidth, screenHeight = getScreenResolution()

	imgui.SetNextWindowPos(imgui.ImVec2(0, 0), imgui.Cond.Always, imgui.ImVec2(0, 0))
	imgui.SetNextWindowSize(imgui.ImVec2(screenWidth, screenHeight), imgui.Cond.Always)
	
	local windowFlags = imgui.WindowFlags.NoTitleBar + imgui.WindowFlags.NoResize + 
	                   imgui.WindowFlags.NoMove + imgui.WindowFlags.NoScrollbar +
	                   imgui.WindowFlags.NoInputs + imgui.WindowFlags.NoBackground +
	                   imgui.WindowFlags.NoBringToFrontOnFocus
	
	NotificationWindowState[0] = true
	imgui.Begin("##notifications", NotificationWindowState, windowFlags)

	local notificationWidth = 400.0
	local notificationHeight = 50.0
	local notificationSpacing = 8.0
	local bottomMargin = 50.0

	local activeNotifications = {}
	local currentTime = os.clock()
	
	for i = #notifications, 1, -1 do
		local notif = notifications[i]
		local elapsed = currentTime - notif.startTime
		local totalDuration = notificationFadeIn + notificationDuration + notificationFadeOut
		
		if elapsed < totalDuration then
			table.insert(activeNotifications, notif)
		else

			table.remove(notifications, i)
		end
	end

	local drawList = imgui.GetWindowDrawList()
	if not drawList then 
		imgui.End()
		return 
	end
	
	local windowPos = imgui.GetWindowPos()


	
	for idx, notif in ipairs(activeNotifications) do
		local elapsed = currentTime - notif.startTime
		local totalDuration = notificationFadeIn + notificationDuration + notificationFadeOut

		local alpha = 1.0
		if elapsed < notificationFadeIn then

			alpha = elapsed / notificationFadeIn
		elseif elapsed < notificationFadeIn + notificationDuration then

			alpha = 1.0
		else

			local fadeOutStart = notificationFadeIn + notificationDuration
			alpha = 1.0 - ((elapsed - fadeOutStart) / notificationFadeOut)
		end


		local positionFromBottom = #activeNotifications - idx + 1

		local baseY = screenHeight - bottomMargin - (notificationHeight + notificationSpacing) * positionFromBottom
		local notificationX = (screenWidth - notificationWidth) / 2.0
		
		local slideDistance = 80.0
		local shiftDistance = notificationHeight + notificationSpacing
		local fadeOutDistance = 30.0
		
		local notificationY = baseY

		if elapsed < notificationFadeIn then

			local fadeProgress = elapsed / notificationFadeIn
			local offsetBelow = slideDistance * (1.0 - fadeProgress)
			notificationY = baseY + offsetBelow

			local totalShiftDown = 0.0
			for otherIdx = 1, idx - 1 do
				local otherNotif = activeNotifications[otherIdx]
				if otherNotif then
					local otherElapsed = currentTime - otherNotif.startTime
					local otherTotalDuration = notificationFadeIn + notificationDuration + notificationFadeOut
					local otherFadeOutStart = notificationFadeIn + notificationDuration

					if otherElapsed >= otherFadeOutStart and otherElapsed < otherTotalDuration then

						local fadeOutProgress = (otherElapsed - otherFadeOutStart) / notificationFadeOut

						totalShiftDown = totalShiftDown + (shiftDistance * fadeOutProgress)
					elseif otherElapsed >= otherTotalDuration then

						totalShiftDown = totalShiftDown + shiftDistance
					end
				end
			end


			notificationY = notificationY + totalShiftDown
		elseif elapsed < notificationFadeIn + notificationDuration then

			notificationY = baseY


			local totalShiftUp = 0.0
			for otherIdx = idx + 1, #activeNotifications do
				local otherNotif = activeNotifications[otherIdx]
				if otherNotif then
					local otherElapsed = currentTime - otherNotif.startTime
					if otherElapsed < notificationFadeIn then

						local fadeProgress = otherElapsed / notificationFadeIn
						totalShiftUp = totalShiftUp + (shiftDistance * fadeProgress)
					end
				end
			end


			local totalShiftDown = 0.0
			for otherIdx = 1, idx - 1 do
				local otherNotif = activeNotifications[otherIdx]
				if otherNotif then
					local otherElapsed = currentTime - otherNotif.startTime
					local otherTotalDuration = notificationFadeIn + notificationDuration + notificationFadeOut
					local otherFadeOutStart = notificationFadeIn + notificationDuration

					if otherElapsed >= otherFadeOutStart and otherElapsed < otherTotalDuration then

						local fadeOutProgress = (otherElapsed - otherFadeOutStart) / notificationFadeOut

						totalShiftDown = totalShiftDown + (shiftDistance * fadeOutProgress)
					elseif otherElapsed >= otherTotalDuration then

						totalShiftDown = totalShiftDown + shiftDistance
					end
				end
			end


			notificationY = baseY - totalShiftUp + totalShiftDown
		else

			local fadeOutStart = notificationFadeIn + notificationDuration
			local fadeOutProgress = (elapsed - fadeOutStart) / notificationFadeOut
			local offsetUp = fadeOutDistance * fadeOutProgress
			notificationY = baseY - offsetUp
		end

		local bgColor = imgui.GetColorU32Vec4(imgui.ImVec4(0.0, 0.0, 0.0, 0.7 * alpha))
		drawList:AddRectFilled(
			imgui.ImVec2(notificationX, notificationY),
			imgui.ImVec2(notificationX + notificationWidth, notificationY + notificationHeight),
			bgColor,
			8.0
		)

		local borderColor = imgui.GetColorU32Vec4(imgui.ImVec4(0.50, 0.28, 0.88, 0.9 * alpha))
		drawList:AddRect(
			imgui.ImVec2(notificationX, notificationY),
			imgui.ImVec2(notificationX + notificationWidth, notificationY + notificationHeight),
			borderColor,
			8.0,
			0,
			2.0
		)

		local textColor = imgui.GetColorU32Vec4(imgui.ImVec4(1.0, 1.0, 1.0, alpha))

		local text = notif.text
		imgui.SetWindowFontScale(1.2)
		local textSize = imgui.CalcTextSize(text)
		imgui.SetWindowFontScale(1.0)

		local textX = notificationX + (notificationWidth - textSize.x) / 2.0
		local textY = notificationY + (notificationHeight - textSize.y) / 2.0

		local shadowColor = imgui.GetColorU32Vec4(imgui.ImVec4(0.0, 0.0, 0.0, 0.8 * alpha))
		imgui.SetWindowFontScale(1.2)
		drawList:AddText(imgui.ImVec2(textX + 2, textY + 2), shadowColor, text)
		drawList:AddText(imgui.ImVec2(textX, textY), textColor, text)
		imgui.SetWindowFontScale(1.0)
	end
	
	imgui.End()
end).HideCursor = function()
	return true
end

function main()
    -- подождать полной инициализации SAMP, иначе вызовы samp* падают (0B23)
    while not isSampLoaded() do wait(200) end
    while not isSampAvailable() do wait(200) end
	loadSettings()
	loadCoords()
	ensureBansFile()
	checkForUpdates()

	if type(sampAddChatMessage) == 'function' then

		local playerName = "друг"

		if PLAYER_PED and doesCharExist(PLAYER_PED) then
			local pcallOk, sampOk, myId = pcall(sampGetPlayerIdByCharHandle, PLAYER_PED)
			if pcallOk and sampOk and myId then
				local name = sampGetPlayerNickname(myId)
				if name and name ~= "" then
					playerName = name
				end
			end
		end


		local colorBotTag = '{AA77FF}'
		local colorNormal = '{CCCCCC}'
		local colorName = '{BB88FF}'
		local colorGray = '{CCCCCC}'
		local colorReset = '{FFFFFF}'
		
		local welcomeText = string.format('%s[BBot v2.0]%s Привет %s%s%s, %sдавай побаним ботов?',
			colorBotTag, colorNormal, colorName, playerName, colorGray, colorGray, colorReset)
		local welcomeMsg = u8:encode(welcomeText)
		sampAddChatMessage(u8:decode(welcomeMsg, 'CP1251'), -1)

        local lowLevelCount = 0
        if isSampAvailable() then
            for i = 0, 1000 do
                if sampIsPlayerConnected(i) then
                    local level = sampGetPlayerScore(i)
                    if level >= 1 and level <= 5 then
                        lowLevelCount = lowLevelCount + 1
                    end
                end
            end
        end

		local countText = string.format('%s[BBot v2.0]%s Воу, сейчас на сервере уже %s%d%s игроков с 1 - 5 уровень!%s',
			colorBotTag, colorNormal, colorName, lowLevelCount, colorNormal, colorReset)
		local countMsg = u8:encode(countText)
		sampAddChatMessage(u8:decode(countMsg, 'CP1251'), -1)

		local motivationText = string.format('%s[BBot v2.0]%s Не спи! Сервер нуждается в тебе!%s',
			colorBotTag, colorNormal, colorReset)
		local motivationMsg = u8:encode(motivationText)
		sampAddChatMessage(u8:decode(motivationMsg, 'CP1251'), -1)
	end
	sampRegisterChatCommand('bbot', function() WinState[0] = not WinState[0] end)
	sampRegisterChatCommand('banbind', function(param)
		waitingForBanKey = true
	end)
	sampRegisterChatCommand('skipbind', function(param)
		waitingForSkipKey = true
	end)
	sampRegisterChatCommand('bupdate', function()
		if updateAvailableVersion then
			UpdateWindowState[0] = true
		elseif updateCheckInProgress then
			local msg = u8('[BBot v2.0] Идёт проверка обновлений...')
			sampAddChatMessage(u8:decode(msg, 'CP1251'), -1)
		else
			local msg = u8('[BBot v2.0] Обновлений нет.')
			sampAddChatMessage(u8:decode(msg, 'CP1251'), -1)
		end
	end)

	sampev.onTogglePlayerSpectating = function(playerid, bool)

		local prevState = wasSpectating
		wasSpectating = bool

		local currentTime = os.clock()
		local timeSinceRe = currentTime - reCommandTime

		if prevState and not bool and timeSinceRe >= 0.5 and isRunning and DecisionOpen[0] then
			wasKickedFromSpectate = true

			sampSendChat("/reoff")
			DecisionOpen[0] = false
			isProcessing = false
			pendingReport = nil
		end
	end

	lua_thread.create(function()
		while true do
			wait(0)
			if not sampIsChatInputActive() then
				if waitingForBanKey then
					local key = getPressedKey()
					if key then
						banKey[0] = key
						waitingForBanKey = false
						saveSettings()
					end
				elseif waitingForSkipKey then
					local key = getPressedKey()
					if key then
						skipKey[0] = key
						waitingForSkipKey = false
						saveSettings()
					end
			elseif waitingForActivationKey then
				local key = getPressedKey()
				if key then
					activationKey[0] = key
					waitingForActivationKey = false
					saveSettings()
				end
				elseif wasKeyPressed(banKey[0]) and DecisionOpen[0] and pendingReport and not sampIsChatInputActive() then

					local currentTime = os.clock()
					local elapsedTime = currentTime - banCountdownStartTime
					local countdownDuration = banCountdownMs[0] / 1000.0
					local remainingTime = countdownDuration - elapsedTime
					if remainingTime > 0 then

					else

						if not isAutoBan[0] then
							performBan()
						end
					end
				elseif wasKeyPressed(skipKey[0]) and DecisionOpen[0] and pendingReport and not sampIsChatInputActive() then

					sampSendChat("/reoff")
					if pendingReport and pendingReport.name then
						skippedPlayers[pendingReport.name] = true
					end
					DecisionOpen[0] = false
					pendingReport = nil
					isProcessing = false
					lastDecisionCloseTime = os.clock() * 1000
		elseif backgroundMode[0] and not isRunning and backgroundPending and wasKeyPressed(activationKey[0]) and not sampIsChatInputActive() then

			-- Активируем слежку по сохраненному кандидату
			local p = backgroundPending
			backgroundPending = nil
			local nowMs = os.clock() * 1000
			local reTime = nil
			if (nowMs - lastCommandTime) >= commandCooldown and (nowMs - lastDecisionCloseTime) >= 500 then
				sampSendChat(string.format('/re %s', p.name))
				lastCommandTime = nowMs
				reTime = os.clock()
				reCommandTime = os.clock()
			end
			pendingReport = { id = p.id, name = p.name, level = p.level, distance = p.distance, ip = 'неизвестно', reTime = reTime }
			DecisionOpen[0] = true
			wasKickedFromSpectate = false
			banCountdownStartTime = os.clock()
			autoBanTriggered = false
				end
			end
		end
	end)

	lua_thread.create(function()
		while true do
			wait(0)
			local currentTime = os.clock()

			if (currentTime - lastReminderCheckTime) >= 30.0 then
				lastReminderCheckTime = currentTime

				local botCount = 0
				for i = 0, 1000 do
					if sampIsPlayerConnected(i) then
						local level = sampGetPlayerScore(i)
						if level >= 1 and level <= 5 then
							botCount = botCount + 1
						end
					end
				end

				if botCount > 25 then
					local timeSinceLastShow = currentTime - lastReminderShowTime
					if timeSinceLastShow >= 300.0 or lastReminderShowTime == 0 then

						reminderBotCount = botCount
						reminderStartTime = currentTime
						lastReminderShowTime = currentTime
					end
				end
			end
		end
	end)
	
	-- Фоновое сканирование: работает только когда скрипт не запущен кнопкой "Начать"
	lua_thread.create(function()
		while true do
			wait(50)
			if backgroundMode[0] and not isRunning and not sampIsChatInputActive() then
				local nowTime = os.clock()
				local myX, myY, myZ = getCharCoordinates(PLAYER_PED)
				local okSelf, okSamp, myId = pcall(sampGetPlayerIdByCharHandle, PLAYER_PED)
				if not okSelf or not okSamp or not myId then goto continue_bg end
				for i = 0, 1000 do
					if not backgroundMode[0] or isRunning then break end
					if sampIsPlayerConnected(i) and i ~= myId then
						local okPed, ped = sampGetCharHandleBySampPlayerId(i)
						if okPed then
							local px, py, pz = getCharCoordinates(ped)
							local last = playerLastPos[i]
							local speedKmh = nil
							if last ~= nil then
								local dt = nowTime - last.t
								if dt > 0 then
									local dx, dy, dz = px - last.x, py - last.y, pz - last.z
									local dist = math.sqrt(dx*dx + dy*dy + dz*dz)
									speedKmh = (dist / dt) * 3.6
								end
							end
							playerLastPos[i] = { x = px, y = py, z = pz, t = nowTime }

							-- Признак бота в фоне: сверхвысокая скорость пешком рядом и низкий уровень
							if speedKmh ~= nil and speedKmh > 500.0 and not isCharInAnyCar(ped) then
								local dxm, dym, dzm = myX - px, myY - py, myZ - pz
								local distanceToMe = math.sqrt(dxm*dxm + dym*dym + dzm*dzm)
								if distanceToMe <= 300.0 then
									local level = sampGetPlayerScore(i)
									if level >= 1 and level <= 5 then
										local lastTrig = playerLastTriggeredAt[i] or 0
										if (nowTime - lastTrig) >= 1.0 then
											playerLastTriggeredAt[i] = nowTime
											local name = sampGetPlayerNickname(i)
											backgroundPending = { id = i, name = name, level = level, distance = distanceToMe }
											local keyName = vkeys.id_to_name(activationKey[0]) or string.format("0x%02X", activationKey[0])
											local decodedName = u8:decode(name, 'CP1251')
											addNotification(string.format(u8'%s возможно бот — нажмите %s', decodedName, keyName))
										end
									end
								end
							end
						end
					end
				end
				::continue_bg::
			end
		end
	end)

	wait(-1)
end

-- Ensure MoonLoader can find the entry point in the global environment
_G.main = main

function getPressedKey()

	if isKeyDown(0x01) then
		while isKeyDown(0x01) do wait(0) end
		return 0x01
	end
	if isKeyDown(0x02) then
		while isKeyDown(0x02) do wait(0) end
		return 0x02
	end
	if isKeyDown(0x04) then
		while isKeyDown(0x04) do wait(0) end
		return 0x04
	end
	if isKeyDown(0x05) then
		while isKeyDown(0x05) do wait(0) end
		return 0x05
	end
	if isKeyDown(0x06) then
		while isKeyDown(0x06) do wait(0) end
		return 0x06
	end

	for key = 1, 256 do
		if isKeyDown(key) then
			while isKeyDown(key) do wait(0) end
			return key
		end
	end
	return nil
end

function wasKeyPressed(key)
	if isKeyDown(key) then
		while isKeyDown(key) do wait(0) end
		return true
	end
	return false
end