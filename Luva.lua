local compile = dofile("Compiler.lua")

local args = {...}
local file, output = args[1], args[2]
local isColor = term.isColor()
local isFolder = fs.isDir(file)

if not file and not output then
	term.setTextColor(isColor and colors.cyan or colors.white)
	print("Interactive Luva prompt.\nType in 'exit' to exit.")
	term.setCursorBlink(true)
	local commandHistory = {}
	while true do
		term.setTextColor(isColor and colors.blue or colors.white)
		term.write("luva")
		term.setTextColor(colors.white)
		term.write("> ")

		-- Totally didn't copy from the Lua program
		local input = read(_, commandHistory, function(sLine)
		    local nStartPos = string.find( sLine, "[a-zA-Z0-9_%.]+$" )
		    if nStartPos then sLine = string.sub( sLine, nStartPos ) end
		    if #sLine > 0 then return textutils.complete( sLine, tEnv ) end
		end)
		commandHistory[#commandHistory + 1] = input

		if input == "exit" then break end
 		local compiled, err = compile({input})

 		if compiled then
	 		local func, err = loadstring(compiled)
			if not func then
				local _, _, _, e = err:match('([^,]+):([^,]+):([^,]+):([^,]+)')
				printError("error:" ..e) 
			else func() end
		else
			printError("error: " ..err)
		end
	end
	return
end

output = output or "compiled"
if not fs.exists(file) then error(file.. " doesn't exist", 2) end

if isFolder then
	local function compileFiles(dir, f_name)
		fs.makeDir(f_name)
		local files = fs.list(dir)
		for i = 1, #files do
			local f = files[i]
			if fs.isDir(dir.."/"..f) then
				compileFiles(dir.."/"..f, f_name.."/"..f)
			else
				local file = fs.open(dir.."/"..f, "r")
				local contents = {}
				repeat
					local line = file.readLine()
					contents[#contents + 1] = line
				until not line
				file.close()

				local compiled, err = compile(contents)
				if not compiled then 
					printError("Unable to compile " ..dir.. "/" ..f.. ": " ..err)
				else
					local file = fs.open(f_name.."/"..f, "w")
					file.write(compiled)
					file.close()
				end
			end
		end
	end
	fs.delete(output); compileFiles(file, output)
else
	local file = fs.open(file, "r")
	local contents = {}
	repeat
		local line = file.readLine()
		contents[#contents + 1] = line
	until not line
	file.close()

	local compiled, err = compile(contents)
	if not compiled then 
		printError(err)
	else
		local func, err = loadstring(compiled)--; print(compiled)
		if not func then printError(err) else func() end
		fs.delete(output)
		local file = fs.open(output, "w")
		file.write(compiled)
		file.close()
	end
end