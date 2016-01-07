local newLexer = dofile("Lexer.lua")
local native_error, rep, sub, tonum = error, string.rep, string.sub, tonumber
local function compile(text)
	local lex, currentToken = newLexer(text); local function nextToken() currentToken = lex() end; nextToken()
	local header = "local _ty, _smt, _bsl, _bsr, _blsr, _bor, _band, _bnot, _bxor = type, setmetatable, bit.blshift, bit.brshift, bit.blogic_rshift, bit.bor, bit.band, bit.bnot, bit.bxor\nlocal function type(o) local ty = _ty(o); return ty == 'table' and o.__type or ty end\nlocal function _twc(v, v2) if v < v2 then return false elseif v == v2 then return nil else return true end end\nlocal function _idn(t1, t2) if type(t1) ~= 'table' or type(t2) ~= 'table' then error('expected [table] <=> [table]', 2) end if #t1 ~= #t2 then return end for k, v in pairs(t1) do if v ~= t2[k] then return end end return true end\n\n"
	local compiled = ""

	local function error(err, section)
		print("Compiled:\n\n" ..compiled.. "\n"); 
		if section then printError(section) end
		native_error(err)
	end

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
				  (accept("(") and "("..table.concat(expList(), ", ")..expect(")", "getIdentifier").."\n") or 
				  (accept(".") and "."..expect(_, "id", "getIdentifier")) or
				  (accept("[") and "["..expression()..expect("]", "getIdentifier")) or
				  accept("...")
		if e then e = e..(e and getIdentifier() or "") end; return e
	end

	local function idList(useTypes)
		local list, types = {}, {}

		repeat
			local id = getIdentifier()
			if id then
				if useTypes and accept(":") then
					types[#types + 1] = {id, expect(_, "id", "idList")}
				end
				list[#list + 1] = id
			end
		until not accept(",")
		return list, types
	end

	function getName()
        local e = accept(_, "id") or (accept(".") and "."..expect(_, "id", "getName"))
		if e then e = e..(e and getName() or "") end; return e
    end

	local function getFunction(ignoreName)
		local f = (not ignoreName and getName() or "")..expect("(", "function")
		local v, t = idList(true); f = f..table.concat(v, ", ")..expect(")", "function").."\n"
		expect("{", "function")
		if t then
			for i = 1, #t do
				local var, type = t[i][1], t[i][2]
				f = f.."local _ = _ty(" ..var.. ") == '" ..type.. "' or error('" ..var.. " must be a " ..type.. " (given a ' .._ty(" ..var.. ").. ')', 2) \n"
			end
		end
		f = f..block()..(expect("}", "function") and "end\n")
		return f
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
		end
		
		if ins(accept("(")) then exp[#exp] = exp[#exp]..expression()..expect(")", "expression: paranthesis") end
		ins(accept("nil") or accept("true") or accept("false") or (accept("-") and "-"..expression()) or (accept("#") and "#"..getIdentifier()) or accept(_, "str") or accept(_, "num") or getIdentifier())

		if ins(accept("function")) then ins(getFunction(true)) end
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
			if accept("===") then exp[i] = "_idn(" ..exp[i]..", "..(expression() or error("expected exp @ identical"))..")"
		elseif accept("~==") then exp[i] = "not _idn(" ..exp[i]..", "..(expression() or error("expected exp @ identical"))..")"
		elseif accept("<=>") then exp[i] = "_twc(" ..exp[i]..", "..(expression() or error("expected exp @ three-way comparison"))..")"
		elseif accept(">>")  then exp[i] = "_bsr(" ..exp[i]..", "..(expression() or error("expected exp @ bshift_right"))..")"
		elseif accept(">>>") then exp[i] = "_blsr("..exp[i]..", "..(expression() or error("expected exp @ blogic_right"))..")"
		elseif accept("<<")  then exp[i] = "_bsl(" ..exp[i]..", "..(expression() or error("expected exp @ bshift_left"))..")"
		elseif accept("&")   then exp[i] = "_band("..exp[i]..", "..(expression() or error("expected exp @ band"))..")"
		elseif accept("|")   then exp[i] = "_bor(" ..exp[i]..", "..(expression() or error("expected exp @ bor"))..")"
		elseif accept("!")   then exp[i] = "_bnot("..exp[i]..", "..(expression() or error("expected exp @ bnot"))..")"
		elseif accept("~")   then exp[i] = "_bxor("..exp[i]..", "..(expression() or error("expected exp @ bxor"))..")" 
		
		elseif accept("++") then exp[i] = exp[i].. " + 1"
		elseif accept("--") then exp[i] = exp[i].. " - 1"

		end

		return table.concat(exp)
	end

	expList = function()
		local list = {}
		repeat
			list[#list + 1] = expression()
		until not accept(",")
		return list
	end

	local function ctable_builder()
		local str = ""
		repeat
			local ids, vars = {}, {}
			repeat local id = accept(_, "id"); if id then ids[#ids + 1] = id end until not accept(",")
			if accept("=") then repeat vars[#vars + 1] = expression() until not accept(",") end
			for i = 1, #ids do
				if vars[i] then
					str = str..ids[i].." = "..vars[i]..", "
				end
			end							
		until #ids == 0
		return str
	end

	local function pctable_builder()
		local str = ""
		repeat
			local ids, vars = {}, {}
			repeat local id = accept(_, "id"); if id then ids[#ids + 1] = id end until not accept(",")
			if accept("=") then repeat vars[#vars + 1] = expression() until not accept(",") end
			for i = 1, #ids do
				if vars[i] then
					str = str.."local "..ids[i].." = "..vars[i].."\n"
				end
			end							
		until #ids == 0
		return str
	end

	statement = function()
		local stat = ""; local function ins(tok, a) if tok then stat = stat..tok..(a or ""); return true end end

		local isLocal = accept("local")
		if not isLocal and ins(accept("if"), " ") then
			ins(expression(), " ")
			ins(expect("{", "statement: if") and "then\n")
			ins(block())
			expect("}", "statement: if")
			while ins(accept("elseif"), " ") do
				ins(expression(), " ")
				ins(expect("{", "statement: elseif") and "then\n")
				ins(block())
				expect("}", "statement: elseif")
			end
			if ins(accept("else"), " ") then
				ins(expect("{", "statement: else") and block()); expect("}", "statement: else")
			end
			ins("end\n")

		elseif not isLocal and ins(accept("do"), "\n") then
			ins(expect("{", "statement: do") and block())
			ins(expect("}", "statement: do") and "end\n")

		elseif not isLocal and ins(accept("for"), " ") then
			ins(expect(_, "id", "statement: for"), " ")
			ins(expect("=", "statement: for"), " ")
			ins(table.concat(expList(), ", "), " ")
			ins(expect("{", "statement: for") and "do\n")
			ins(block(), "\n")
			ins(expect("}", "statement: for") and "end\n")

		elseif not isLocal and accept("repeat") then
			if ins(accept("while") and "repeat ") then
				local condition = expression()
				expect("{", "statement: repeat until")
				ins(block())
				ins(expect("}", "statement: repeat until") and "\nuntil not(" ..condition.. ")\n")

			elseif ins(accept("until") and "repeat ") then
				local condition = expression()
				expect("{", "statement: repeat until")
				ins(block())
				ins(expect("}", "statement: repeat until") and "\nuntil " ..condition.. "\n")

			else
				ins(expect("{", "statement: repeat") and "for __ = 0, 1, 0 do\n")
				ins(block())
				ins(expect("}", "statement: repeat") and "end\n")
			end

		elseif not isLocal and ins(accept("while"), " ") then
			ins(expression(), " ")
			ins(expect("{", "statement: while") and "do\n")
			ins(block())
			ins(expect("}", "statement: while") and "end\n")

		elseif not isLocal and ins(accept("until") and "while ") then
			ins("not ("..expression()..")", " ")
			ins(expect("{", "statement: until") and "do\n")
			ins(block())
			ins(expect("}", "statement: until") and "end\n")

		elseif not isLocal and ins(accept("guard") and "if ") then
			ins("not ("..expression()..") "..(expect("else", "statement: guard") and "then\n"))
			ins(expect("{", "statement: guard") and block())
			ins(expect("}", "statement: guard") and "return\nend\n")

		elseif not isLocal and accept("try") then
			ins(expect("{", "statement: try") and "do\n")
			ins("local ok, e = pcall(function()\n"..block().."end)\n")
			expect("}", "statement: try")
			local stat = "if"
			local usedCatch = false
			while accept("catch") do
				local str = accept(_, "str")
				if not usedCatch then ins("local _, _, e = e:match('([^,]+):([^,]+):([^,]+)'); e = e:sub(2)\n"); usedCatch = true; end
				expect("{", "statement: try")
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
				expect("}", "statement: try")
			end
			ins(stat == "elseif" and "end\n" or "")
			ins("end\n")

		elseif not isLocal and accept("with") then
			ins("do\nlocal " .. table.concat(idList(), ", ") .. (expect("=", "statement: with") and " = "..table.concat(expList(), ", ")), "\n")
			ins(expect("{", "statement: with") and "local ok, e = pcall(function()\n"..block().."end)\n")
			expect("}", "statement: with")
			local stat = "if"
			local usedCatch = false
			while accept("catch") do
				local str = accept(_, "str")
				if not usedCatch then ins("local _, _, e = e:match('([^,]+):([^,]+):([^,]+)'); e = e:sub(2)\n"); usedCatch = true; end
				expect("{", "statement: with")
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
				expect("}", "statement: with")
			end
			ins(stat == "elseif" and "end\n" or "")
			ins("end\n")

		elseif not isLocal and ins(accept("return"), " ") then
			ins(table.concat(expList(), ", ").."\n")

		elseif not isLocal and ins(accept("break"), "\n") then

		elseif ins(accept("function") and (isLocal and "local " or "").."function", " ") then
			ins(getFunction(), "\n")
		
		elseif accept("overloaded") then
			expect("function", "statement: overloaded")
			local func = getIdentifier()
			ins((isLocal and "local " or "").. func.. " = {\n")
			expect(":", "statement: overloaded")
			repeat
				expect("(", "statement: overloaded"); local v, t = idList()
				ins("[" ..((#v == 1 and v[1] == "..." and -1) or #v).. "] = function(" ..table.concat(v, ", ").. ")")
				expect(")", "statement: overloaded"); expect("{", "statement: overloaded")
				if t then
					for i = 1, #t do
						local var, type = t[i][1], t[i][2]
						ins("local _ = _ty(" ..var.. ") == '" ..type.. "' or error('" ..var.. " must be a " ..type.. " (given a ' .._ty(" ..var.. ").. ')', 2) \n")
					end
				end
				ins(block())
				expect("}", "statement: overloaded")
				ins("end,\n") 
			until not accept(",")
			ins("}\n")
			-- Maybe put (...) function in code below to allow __index to be stopped?
			ins("_smt("..func..", {\n__call = function(t, ...) local args = {...}; return (t[#args] or t[-1] or error('overloaded function "..func.." cannot take ' ..#args.. ' arguments'))(unpack(args)) end,\n__newIndex = function() error('attempt to index "..func.." (a function value)') end,\n__type = 'function'})")

		-- Messy class code, I know.
		-- Private static???
		elseif accept("class") then
			local name, type = getName(), "object"; ins(isLocal and ("local "..name) or "", "\n")
			if accept("(") then type = expect(_, "id", "statement: class"); expect(")") end
			if accept("extends") then
				local parent = expect(_, "id", "statement: extends")
			else
				ins(expect("{", "statement: class") and "do\n")
				local public, public_static, public_shared = "local self\n self = {__type = '"..type.."', ", "", ""
				local private, private_shared = "", ""
				
				-- Super should be defined as:
				-- local super = _smt({}, classToInheritFrom)

				-- Metamethods:
				-- methamethod add(a: number, b: number) { // Automatically converted to __add = function(a, b)... 
				-- 		return a + b
				-- }

				local function class_exp()
					if accept("public") then
						accept(":")
						if accept("static") then
							accept(":")
							public_static = public_static..ctable_builder()

						elseif accept("shared") then
							accept(":")
							public_shared = public_shared..ctable_builder()

						else
							public = public..ctable_builder()
						end

					elseif accept("private") then
						accept(":")
						if accept("shared") then
							accept(":")
							private_shared = private_shared..pctable_builder()
						else
							private = private..pctable_builder()
						end

					else
						return true
					end
				end
				repeat until class_exp()

				ins(public_shared ~= "" and "local public_shared = {" ..sub(public_shared, 1, #public_shared - 2).. "}\n")
				ins(public_static ~= "" and "local public_static = {" ..sub(public_static, 1, #public_static - 2).. "}\n")
				ins(private_shared ~= "" and private_shared.. "\n")

				-- List all shared functions here
				-- List all static functions here

				ins(name.. " = function()\n")
				ins(private ~= "" and private.. "\n")
				ins(sub(public, 1, #public - 2).. "}\n")

				-- List all private functions here
				-- List all public functions here

				ins("if __init then __init() end\n") -- Perhaps move __init() function to be here?
				if public_static ~= "" or public_shared ~= "" then
					ins("return _smt(self, {\n__newindex = function(t, k, v)\n")
					ins("rawset("..(public_static ~= "" and "(public_static[k] and error('cannot modify static variable ' ..k, 2)) or " or "")..(public_shared ~= "" and "(public_shared[k] and public_shared) or " or "").."self, k, v)\nend,\n")
					ins("__index = function(t, k)\nreturn " ..(public_shared ~= "" and "public_shared[k] or " or "")..(public_static ~= "" and "public_static[k] or " or "").."self[k]\nend})\nend")
				else
					ins("return self\nend")
				end
				ins(expect("}", "statement: class") and "\nend\n")
			end
		else
			if isLocal then
				ins("local " .. table.concat(idList(), ", "), " ")
				ins(accept("=") and "= "..table.concat(expList(), ", "), "\n")
			else
				local vars = idList(); ins(table.concat(vars, ", "), " ")

				if accept("=") then
					ins("= "..table.concat(expList(), ", "), "\n")
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

					elseif accept("&=") then ins("= _band(" ..vars[1].. "," ..expression().. ")\n")
					elseif accept("|=") then ins("= _bor(" ..vars[1].. "," ..expression().. ")\n")
					elseif accept("!=") then ins("= _bnot(" ..vars[1].. "," ..expression().. ")\n")
					elseif accept(">>=") then ins("= _bsr(" ..vars[1].. "," ..expression().. ")\n")
					elseif accept(">>>=") then ins("= _blsr(" ..vars[1].. "," ..expression().. ")\n")
					elseif accept("<<=") then ins("= _bsl(" ..vars[1].. "," ..expression().. ")\n") end
				end
			end
		end
		accept(";"); return stat ~= " " and stat
	end

	block = function()
		local b = ""
		while currentToken do
			local stat = statement(); if not stat then break end
			b = b..stat; compiled = compiled..stat
		end
		return b
	end

	return header..block()
end











term.clear()
term.setCursorPos(1, 1)

local args = {...}
local arg1, arg2 = args[1], args[2]

if not arg1 or arg1 == "help" or arg1 == "-h" then printError("Usage: [LuvaFile] <OutputFile>"); return end
if not fs.exists(arg1) then printError(file.. " doesn't exist. Please give a valid file location."); return end

local file = fs.open(arg1, "r")
local contents = {}
repeat
	local line = file.readLine()
	contents[#contents + 1] = line
until not line
file.close()

local compiled = compile(contents)
local ok, err = loadstring(compiled)

if not ok then
	print(compiled)
	printError(err)
	return
end

ok()

if arg2 then
	fs.delete(arg2)
	local file = fs.open(arg2, "w")
	file.write(compiled)
	file.close()
end