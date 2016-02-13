local newLexer = dofile("Lexer.lua")

--[[
local _loadedFiles = {}
local load, pc, exists = loadfile, pcall, fs.exists
local function require(fileName, ...)
	if _loadedFiles[fileName] then return _loadedFiles[fileName] end
	if not exists(fileName) then error("failed to require " ..fileName.. " (file doesn't exist).") end
	
	local ok, err = load(fileName); if not ok then error("failed to require " ..fileName.. " (" ..err.. ")") end
	local ok, loadedTable = pc(ok, ...); if not ok then error("failed to require " ..fileName.. " (" ..loadedTable.. ")") end

	_loadedFiles[fileName] = type(loadedTable) == "table" and loadedTable or error("failed to require " ..fileName.. " (file must return a table).")
	return _loadedFiles[fileName]
end
--]]

local useCustomType = false
local headers = {
	{false, "_ty", "type"}, -- 1
	{false, "_smt", "setmetatable"}, -- 2

	{false, "_bsl", "bit.blshift"}, -- 3
	{false, "_bsr", "bit.brshift"}, -- 4
	{false, "_blsr", "bit.blogic_rshift"}, -- 5
	{false, "_bor", "bit.bor"}, -- 6
	{false, "_band", "bit.band"}, -- 7
	{false, "_bnot", "bit.bnot"}, -- 8
	{false, "_bxor", "bit.bxor"}, -- 9

	{false, "_rs", "rawset"}, -- 10
	{false, "require", "function(fileName, ...) end"}, -- 11

	{false, "_twc", "function(v, v2) if v < v2 then return false elseif v == v2 then return nil else return true end end"}, -- 12
	{false, "_idn", "function(t1, t2) if type(t1) ~= 'table' or type(t2) ~= 'table' then error('expected [table] <=> [table]', 2) end if #t1 ~= #t2 then return end for k, v in pairs(t1) do if v ~= t2[k] then return end end return true end"} -- 13
}

local function clearFileHeader()
	for i = 1, #headers do headers[i][1] = false end
end

local function getFileHeader()
	local headerLeft, headerRight  = "", ""
	for i = 1, #headers do
		local h = headers[i]
		if h[1] then
			--print("Found header! " ..h[2])
			headerLeft = headerLeft..h[2]..", "
			headerRight = headerRight..h[3]..", "
		end
	end
	return headerLeft ~= "" and "local "..headerLeft:sub(1, #headerLeft - 2).." = "..headerRight:sub(1, #headerRight - 2)..((useCustomType and "; local _ty2 = _ty; _ty = function(o) local ty = _ty2(o); return ty == 'table' and o.__type or ty end" or "")).."\n\n" or ""
end

-- I really need to clean this up, annoying to look at...
local rep, sub, insert = string.rep, string.sub, table.insert
return function(text)
	local errored = false; local function error(err, section) errored = (section and section..": " or "")..err end
	local lex, indent, currentToken = newLexer(text), ""; local function nextToken() currentToken = lex() end; nextToken()
	local function indent()	indent = indent.."    " end; local function unindent() indent = sub(indent, 4) end

	local function accept(token, type, getLine)
		if not currentToken then return end; local tok, ty, l = currentToken[1], currentToken[2], currentToken[3]
		return (tok == token or ty == type) and (nextToken() or true) and tok, getLine and l
	end

	local function expect(token, type, s)
		local accepted, errLine = accept(token, type, true)
		return accepted or error("expected '" ..(token or type).. "', got " ..tostring(currentToken and currentToken[1] or nil).. " @ line " ..(errLine or "?"), type or s)
	end

	local expression, statement, block, expList
	local function getIdentifier()
		local e = accept(_, "id") or 
				  (accept("(") and "("..concat(expList(), ", ")..expect(")", "getIdentifier").."\n") or 
				  (accept(".") and "."..expect(_, "id", "getIdentifier")) or
				  (accept("[") and "["..expression()..expect("]", "getIdentifier")) or
				  accept("...")
		if e then e = e..(e and getIdentifier() or "") end; return e
	end

	-- When I redo this function, be sure to return a string for the
	-- 'types' and 'default' so I don't have to keep doing it manually.
	-- Of course, give it a 'self' option for functions and classes.
	local function idList(useTypes)
		local list, types, default, slot = {}, {}, {}, 0

		repeat
			local id = getIdentifier()
			if id then
				slot = slot + 1
				if useTypes then
					if accept(":") then
						headers[1][1] = true
						types[slot] = {id, expect(_, "id", "idList")}
					end

					if accept("=>") then
						default[slot] = expression() or error("expected expression, got nil")
					end
				end
				list[slot] = id
			end
		until not accept(",")
		return list, types, default
	end

	function getName()
        local e = accept(_, "id") or (accept(".") and "."..expect(_, "id", "getName"))
		if e then e = e..(e and getName() or "") end; return e
    end

	local function getFunction(ignoreName, useSelf)
		local f = (not ignoreName and getName() or "")..expect("(", "function")
		local v, t = idList(true); if useSelf then insert(v, 1, "self"); if t then insert(t, 1, {}) end end
		f = f..concat(v, ", ")..expect(")", "function").."\n"
		expect("{", "function")
		local usedType, var, ty = false
		if t then
			for i = 1, #t do
				ty = t[i][2]
				if ty then
					if not usedType then f = f.."local _ = "; usedType = true end
					var = t[i][1]
					f = f.."(_ty(" ..var.. ") == '" ..ty.. "' or error('" ..var.. " must be a " ..ty.. " (given a ' .._ty(" ..var.. ").. ')', 2))" ..(i ~= #t and " or " or "")
				end
			end
			if usedType then f = f.."\n" end
		end
		f = f..block()..(expect("}", "function") and "end")
		return f
	end

	local function getIdentifier2()
		local e = accept(_, "id") or 
				  (accept("(") and "("..concat(expList(), ", ")..expect(")", "getIdentifier").."\n") or 
				  (accept(".") and "."..expect(_, "id", "getIdentifier")) or
				  (accept(":") and ":"..expect(_, "id", "getIdentifier")) or
				  (accept("[") and "["..expression()..expect("]", "getIdentifier")) or
				  accept("...")
		if e then e = e..(e and getIdentifier2() or "") end; return e
	end

	expression = function()
		local exp = {}; local function ins(tok) if tok then exp[#exp + 1] = tok; return true end end
		if ins(accept("[") and "{") then
			repeat
				local useBracket = accept(":")
				local e = expression()
				local isInd = accept(":")
				local str = sub(e, 1, 1); str = str == "'" or str == '"'
				local num = tonum(e)

				if isInd then
					if str or useBracket or num then e = "["..e.."]" end
					ins(e.. " = "..expression())
				else ins(e) end
			until not ins(accept(",") and ", ") 
			expect("]", "expression: table"); ins("}")
			return concat(exp)
		end
		
		if ins(accept("(")) then exp[#exp] = exp[#exp]..expression()..expect(")", "expression: paranthesis") end
		ins(accept("nil") or accept("true") or accept("false") or (accept("-") and "-"..expression()) or (accept("#") and "#"..getIdentifier2()) or accept(_, "str") or accept(_, "num") or getIdentifier2())

		if ins(accept("function")) then ins(getFunction(true), "\n") end
		if accept("@") then 
			local function getNumber(val)
				local num = math.floor(expect(_, "num", "expression: @")); expect("]", "expression: @")
				if accept("[") then
					local table = getNumber(val)
					return "{" ..rep(table, num-1)..sub(table, 1, #table - 1).. "},"
				else return "{" ..rep(val..",", num - 1)..val.."}," end
			end

			local val; if accept(":") then val = expression(); expect(":", "expression: @") end
			local table = expect("[", "expression: @") and getNumber(tostring(val))
			ins(sub(table, 1, #table - 1))
		end

		local esym = accept("^") or accept("%") or accept("*") or accept("/") or accept("+") or accept("-") or
					 accept(">") or accept(">=") or accept("<") or accept("<=") or accept("==") or accept("~=") or
					 accept("or") or accept("and") or accept("not") or accept("..")

		if esym then ins(" "..esym.." "..(expression() or "")) end; local i = #exp-- ins(accept(":") and (":"..(expression() or "")) or "")
			if accept("===") then headers[13][1] = true; exp[i] = "_idn(" ..exp[i]..", "..(expression() or error("expected exp @ identical"))..")"
		elseif accept("~==") then headers[13][1] = true; exp[i] = "not _idn(" ..exp[i]..", "..(expression() or error("expected exp @ identical"))..")"
		elseif accept("<=>") then headers[12][1] = true; exp[i] = "_twc(" ..exp[i]..", "..(expression() or error("expected exp @ three-way comparison"))..")"
		elseif accept(">>")  then headers[4][1] = true; exp[i] = "_bsr(" ..exp[i]..", "..(expression() or error("expected exp @ bshift_right"))..")"
		elseif accept(">>>") then headers[5][1] = true; exp[i] = "_blsr("..exp[i]..", "..(expression() or error("expected exp @ blogic_right"))..")"
		elseif accept("<<")  then headers[3][1] = true; exp[i] = "_bsl(" ..exp[i]..", "..(expression() or error("expected exp @ bshift_left"))..")"
		elseif accept("&")   then headers[7][1] = true; exp[i] = "_band("..exp[i]..", "..(expression() or error("expected exp @ band"))..")"
		elseif accept("|")   then headers[6][1] = true; exp[i] = "_bor(" ..exp[i]..", "..(expression() or error("expected exp @ bor"))..")"
		elseif accept("!")   then headers[8][1] = true; exp[i] = "_bnot("..exp[i]..", "..(expression() or error("expected exp @ bnot"))..")"
		elseif accept("~")   then headers[9][1] = true; exp[i] = "_bxor("..exp[i]..", "..(expression() or error("expected exp @ bxor"))..")" 
		
		elseif accept("++") then exp[i] = exp[i].. " + 1"
		elseif accept("--") then exp[i] = exp[i].. " - 1" end

		return concat(exp)
	end

	expList = function()
		local list = {}
		repeat
			list[#list + 1] = expression()
		until not accept(",")
		return list
	end

	local function ctable_builder(v, isMetamethod, p)
		local str, id, var = ""
		local ids, vars, list = {}, {}, ""

		local function continue()
			local foundIDs = false
			repeat 
				id = accept(_, "id") 
				if id then 
					ids[#ids + 1] = id; foundIDs = true 
					if v then list = list..id.." = "..v..", " end
				end 
			until not accept(",")

			if foundIDs and accept("=") then
				repeat 
					vars[#vars + 1] = expression() or "nil"
				until not accept(",")
				foundIDs = false
			end

			if accept("function") then
				local name = expect(_, "id")
				ids[#ids + 1] = name
				vars[#vars + 1] = "function"..getFunction(true, not (isMetamethod or p))
				if v then list = list..name.." = "..v..", " end
				continue()
			end
		end
		continue()

		local s, e = (isMetamethod and "__") or (p and "local ") or "", p and "\n" or ", "
		for i = 1, #ids do str = str..s..ids[i].." = "..vars[i]..e end
		return str, list
	end

	statement = function()
		local stat = ""; local function ins(tok, a) if tok then stat = stat..tok..(a or ""); return true end end

		local isLocal = accept("local")
		if not isLocal and ins(accept("if"), " ") then
			ins(expression(), " ")
			ins(expect("{", "if") and "then\n")
			ins(block())
			expect("}", "if")
			while ins(accept("elseif"), " ") do
				ins(expression(), " ")
				ins(expect("{", "elseif") and "then\n")
				ins(block())
				expect("}", "elseif")
			end
			if ins(accept("else"), " ") then
				ins(expect("{", "else") and block()); expect("}", "else")
			end
			ins("end\n")

		elseif not isLocal and ins(accept("unless") and "if not (") then
			ins(expression(), ") ")
			ins(expect("{", "unless") and "then\n")
			ins(block())
			ins(expect("}", "unless") and "end\n")

		elseif not isLocal and ins(accept("do"), "\n") then
			ins(expect("{", "do") and block())
			ins(expect("}", "do") and "end\n")

		elseif not isLocal and ins(accept("for"), " ") then
			ins(expect(_, "id", "for"), " ")
			ins(expect("=", "for"), " ")
			ins(concat(expList(), ", "), " ")
			ins(expect("{", "for") and "do\n")
			ins(block(), "\n")
			ins(expect("}", "for") and "end\n")

		elseif not isLocal and accept("repeat") then
			if ins(accept("while") and "repeat ") then
				local condition = expression()
				expect("{", "repeat until")
				ins(block())
				ins(expect("}", "repeat until") and "\nuntil not(" ..condition.. ")\n")

			elseif ins(accept("until") and "repeat ") then
				local condition = expression()
				expect("{", "repeat until")
				ins(block())
				ins(expect("}", "repeat until") and "\nuntil " ..condition.. "\n")

			else
				ins(expect("{", "repeat") and "for __ = 0, 1, 0 do\n")
				ins(block())
				ins(expect("}", "repeat") and "end\n")
			end

		elseif not isLocal and ins(accept("while"), " ") then
			ins(expression(), " ")
			ins(expect("{", "while") and "do\n")
			ins(block())
			ins(expect("}", "while") and "end\n")

		elseif not isLocal and ins(accept("until") and "while ") then
			ins("not ("..expression()..")", " ")
			ins(expect("{", "until") and "do\n")
			ins(block())
			ins(expect("}", "until") and "end\n")

		elseif not isLocal and ins(accept("guard") and "if ") then
			ins("not ("..expression()..") "..(expect("else", "guard") and "then\n"))
			ins(expect("{", "guard") and block())
			ins(expect("}", "guard") and "return\nend\n")

		elseif not isLocal and accept("try") then
			ins(expect("{", "try") and "do\n")
			ins("local ok, e = pcall(function()\n"..block().."end)\n")
			expect("}", "try")
			local stat = "if"
			local usedCatch = false
			while accept("catch") do
				local str = accept(_, "str")
				if not usedCatch then ins("local _, _, e = e:match('([^,]+):([^,]+):([^,]+)'); e = e:sub(2)\n"); usedCatch = true; end
				expect("{", "try")
				if str then
					if stat == "if" then
						ins("if e == " ..str.. " then\n")
						stat = "elseif"
					else
						ins("elseif e == " ..str.. " then\n")
					end
				else
					if stat == "elseif" then
						ins("else\n")
					end
				end
				ins(block())
				expect("}", "try")
			end
			ins(stat == "elseif" and "end\n" or "")
			ins("end\n")

		elseif not isLocal and accept("with") then
			ins("do\nlocal " ..concat(idList(), ", ") .. (expect("=", "with") and " = "..concat(expList(), ", ")), "\n")
			ins(expect("{", "with") and "local ok, e = pcall(function()\n"..block().."end)\n")
			expect("}", "with")
			local stat = "if"
			local usedCatch = false
			while accept("catch") do
				local str = accept(_, "str")
				if not usedCatch then ins("local _, _, e = e:match('([^,]+):([^,]+):([^,]+)'); e = e:sub(2)\n"); usedCatch = true; end
				expect("{", "with")
				if str then
					if stat == "if" then
						ins("if e == " ..str.. " then\n")
						stat = "elseif"
					else
						ins("elseif e == " ..str.. " then\n")
					end
				else
					if stat == "elseif" then
						ins("else\n")
					end
				end
				ins(block())
				expect("}", "with")
			end
			ins(stat == "elseif" and "end\n" or "")
			ins("end\n")

		elseif not isLocal and ins(accept("return"), " ") then
			ins(concat(expList(), ", ").."\n")

		elseif not isLocal and ins(accept("break"), "\n") then

		elseif ins(accept("function") and (isLocal and "local " or "").."function", " ") then
			ins(getFunction(), "\n")
		
		elseif accept("overloaded") then
			expect("function", "overloaded function")
			local func = getIdentifier()
			ins((isLocal and "local " or "").. func.. " = {\n")
			expect(":", "overloaded function")
			repeat
				expect("(", "overloaded function"); local v, t = idList()
				ins("[" ..((#v == 1 and v[1] == "..." and -1) or #v).. "] = function(" ..concat(v, ", ").. ")")
				expect(")", "overloaded function"); expect("{", "overloaded function")
				local var, ty
				if t then
					ins("local _ = ")
					for i = 1, #t do
						ty = t[i][2]
						if ty then
							var = t[i][1]
							ins("(_ty(" ..var.. ") == '" ..ty.. "' or error('" ..var.. " must be a " ..ty.. " (given a ' .._ty(" ..var.. ").. ')', 2))" ..(i ~= #t and " or " or ""))
						end
					end
					ins("\n")
				end
				ins(block()..(expect("}", "overloaded function") and "end,\n"))
			until not accept(",")
			headers[2][1] = true; useCustomType = true
			ins("}\n_smt("..func..", {\n__call = function(t, ...) local args = {...}; return (t[#args] or t[-1] or error('overloaded function "..func.." cannot take ' ..#args.. ' arguments'))(unpack(args)) end,\n__newIndex = function() error('attempt to index "..func.." (a function value)') end,\n__type = 'function'})")

		-- Cleaned up a bit.
		elseif accept("class") then
			local name, type, parent, super = getName(), "object"; useCustomType = true
			if not string.find(name, "%.") and isLocal then ins("local "..name.."\n") end
			local v, t, d; if accept("(") then v, t, d = idList(true); expect(")", "class") end
			if accept("@") then type = expect(_, "id", "class") end
			if accept("extends") then parent = expect(_, "id", "extends") end
			ins(expect("{", "class") and "do\n")

			if parent then
				super = "local super = " ..parent.. "("

				if accept("@") then
					local property = expect(_, "id", "class")
					if property == "super" then
						expect("(", "class")
						super = super..concat(expList(), ", ")
						expect(")", "class")

					else error("class: unknown property " ..property) end
				end
			end

			local self, mt, lookup, private, private_shared = "{__type = '"..type.. "', ", "", "", "", ""
			local usesShared, usesStatic, usesPrivate = false, false, false

			while true do
				if accept("public") then
					if accept("static") then
						local usesMetamethods, usesStatic = accept("metamethod"), true; accept(":")
						local p, l = ctable_builder(1, usesMetamethods)
						mt, lookup = mt..p, lookup..l

					elseif accept("shared") then
						local usesMetamethods, usesShared = accept("metamethod"), true; accept(":")
						local p, l = ctable_builder(2, usesMetamethods)
						mt, lookup = mt..p, lookup..l

					else
						local usesMetamethods = accept("metamethod"); accept(":"); 
						if usesMetamethods then
							mt = mt..ctable_builder(_, true)
						else
							self = self..ctable_builder()
						end
					end

				elseif accept("private") then
					if accept("shared") then
						accept(":")
						private_shared = private_shared..ctable_builder(_, _, true)

					else
						accept(":"); usesPrivate = true
						private = private..ctable_builder(_, _, true)
					end

				else
					break
				end
			end

			ins(private_shared ~= "" and private_shared.. "\n")
			if mt ~= "" then
				headers[10][1] = true; headers[2][1] = true
				ins("local __lookup = {" ..sub(lookup, 1, #lookup - 2).. "}\nlocal __mt = {" ..sub(mt, 1, #mt - 2).. "}\n\n")
				--if parent then ins("_smt(__mt, super)") end
				ins("\n__mt.__index = __mt\n__mt.__newindex = function(t, k, v) "..(
					(usesShared and usesStatic and "_rs(__lookup[k] and (__lookup[k] == 2 and __public or error('cannot modify static ' ..type(__mt[k]).. ' ' ..k)) or t, k, v)") or
					(usesShared and "_rs(__lookup[k] and __public or t, k, v)") or
					"_rs(__lookup[k] and error('cannot modify static ' ..type(__mt[k]).. ' ' ..k) or t, k, v)").." end\n\n")
			end
			
			ins(name.. " = function(" ..(v and concat(v, ", ") or "").. ")\n")

			local var, ty, de
			if t then
				local pre, nex = "", ""
				for i = 1, #v do
					ty, de = t[i] and t[i][2], d[i]
					if ty and de then
						var = v[i]
						nex = nex..var.." = "..var.. " and (_ty(" ..var.. ") == '" ..ty.. "' or error('" ..var.. " must be a " ..ty.. " (given a ' .._ty(" ..var.. ").. ')', 2)) or " ..de.. "\n"

					elseif ty then
						var = v[i]
						pre = pre.."(_ty(" ..var.. ") == '" ..ty.. "' or error('" ..var.. " must be a " ..ty.. " (given a ' .._ty(" ..var.. ").. ')', 2)) or"

					elseif de then
						var = v[i]
						nex = nex..var.." = "..var.." or "..de.."\n"
					end
				end
				ins((pre ~= "" and "local _ = "..sub(pre, 1, #pre - 3).."\n" or "")..(nex ~= "" and nex.."\n" or ""))
			end

			if super then ins("\n" ..super.. "); super.__index = super\n") end
			if usesPrivate then ins("local self\n" ..private.. "\nself = " ..sub(self, 1, #self - 2).. "}\n") end

			--[[ Future optimizations:
				Move the code from __init() to here to remove function overhead.

				If there isn't any __init, or functions that refer to 'self,' then I shouldn't
				Redeclare self, and I should put it in the 'return' line.
			--]]

			local s = usesPrivate and "self" or sub(self, 1, #self - 2).. "}"
			local m = super and "_smt(__mt, super)" or "__mt"
			if usesPrivate then ins("if init then init() end\n") end
			ins(mt ~= "" and "return _smt(" ..s.. ", " ..m.. ")\nend" or "return " ..s.. "\nend")
			ins(expect("}", "class") and "\nend\n\n")

		else
			if isLocal then
				ins("local " ..concat(idList(), ", "), " ")
				ins(accept("=") and "= "..concat(expList(), ", "), "\n")

			else
				local vars = idList(); ins(concat(vars, ", "), " ")

				if accept("=") then
					ins("= "..concat(expList(), ", "), "\n")

				elseif #vars == 1 then
						if accept("++") then ins("= " ..vars[1].. " + 1\n")
					elseif accept("--") then ins("= " ..vars[1].. " - 1\n")
					elseif accept("+=") then ins("= " ..vars[1].. " + " ..expression().. "\n")
					elseif accept("-=") then ins("= " ..vars[1].. " - " ..expression().. "\n")
					elseif accept("*=") then ins("= " ..vars[1].. " * " ..expression().. "\n")
					elseif accept("/=") then ins("= " ..vars[1].. " / " ..expression().. "\n")
					elseif accept("%=") then ins("= " ..vars[1].. " % " ..expression().. "\n")
					elseif accept("^=") then ins("= " ..vars[1].. " ^ " ..expression().. "\n")
					elseif accept(".=") then ins("= " ..vars[1].. ".." ..expression().. "\n")

					elseif accept("&=") then headers[7][1] = true; ins("= _band(" ..vars[1].. "," ..expression().. ")\n")
					elseif accept("|=") then headers[6][1] = true; ins("= _bor(" ..vars[1].. "," ..expression().. ")\n")
					elseif accept("!=") then headers[8][1] = true; ins("= _bnot(" ..vars[1].. "," ..expression().. ")\n")
					elseif accept(">>=") then headers[4][1] = true; ins("= _bsr(" ..vars[1].. "," ..expression().. ")\n")
					elseif accept(">>>=") then headers[5][1] = true; ins("= _blsr(" ..vars[1].. "," ..expression().. ")\n")
					elseif accept("<<=") then headers[3][1] = true; ins("= _bsl(" ..vars[1].. "," ..expression().. ")\n") end
				end
			end
		end
		return stat ~= " " and stat
	end

	block = function()
		local b = ""
		while currentToken do
			local stat = statement()
			if not stat then break end
			if errored then return end
			accept(";"); b = b..stat
		end
		return b
	end

	local file = block()
	if errored then return false, errored end
	local result = getFileHeader()..file
	clearFileHeader(); return result, false
end