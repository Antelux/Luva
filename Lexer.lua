local find, sub, remove, concat, tonum = string.find, string.sub, table.remove, table.concat, tonumber
local exprs = { -- Commented out keywords are ones that have no functionality yet.
	"if", "elseif", "else", "while", "repeat", "until", "for",
	"return", "break", "true", "false", "nil", "local", 
	"static","shared", "public", "private", "function", --"switch",
	"overloaded", "class", "do", --"extension", "extends",
	"and", "or", "not", "guard", "metamethod", --"in"
}
local token_exprs = {}; for i = 1, #exprs do token_exprs[exprs[i]] = true end

return function(text)
	local position, tokens, chars, base, insert, token = 0, {}, {}, 10, table.insert
	local inComment, skip = false, false

	-- Make this better
	for l = 1, #text do
		for i = 1, #text[l] do 
			if inComment then
				if sub(text[l], i, i) == "*" and sub(text[l], i + 1, i + 1) == "/" then inComment, skip = false, true end
			else
				if skip then skip = false
				else
					local char = sub(text[l], i, i)
					local next = sub(text[l], i + 1, i + 1)
					if char == "/" then
							if next == "/" then break 
						elseif next == "*" then inComment = true
						else chars[#chars + 1] = {char, l} end
					else
						chars[#chars + 1] = {char, l}
					end
				end
			end
		end
		chars[#chars + 1] = {" ", l}
	end

	local function peek() return chars[1] and chars[1][1] or "" end
	local function nextChar() local c = remove(chars, 1); return c and c[1] end
	local function nextToken(pattern, once)
		if once then return (chars[1] and find(chars[1][1], pattern) and nextChar()) or "" end
		local token = ""
		while chars[1] and find(chars[1][1], pattern) do
			token = token..nextChar()
		end
		return token 
	end

	local function isNumber()
		token = nextToken("-", true)..nextToken("%d")
		if token == "0" then
			local next = peek()
			if next == "x" then nextChar(); token, base = token.."x"..nextToken("%x"), 16
			elseif next == "b" then nextChar(); token, base = nextToken("[0-1]"), 2
			else token, base = token..nextToken("%.", true)..nextToken("%d"), 10 end
		elseif token ~= "" then
			token, base = token..nextToken("%.", true)..nextToken("%d"), 10
			if token == "-" then insert(chars, 1, {"-", chars[1][2]}); return false end
		end

		return token ~= ""
	end

	local function isWhitespace()
		return find(chars[1][1], "%s")
	end

	local function isIdentifier()
		token = nextToken("[%a%d_]")
		return token ~= ""
	end

	local function isSymbol()
		token = nextToken("[%[%]%(%)@#{};:,]", true)
		token = token == "" and nextToken("[%%%+%-%*%^%.<>=/!~|&]") or token
		return token ~= ""
	end

	local function isString()
		token = ""
		local quote = nextChar(); quote = (quote == "'" and "'") or (quote == '"' and '"')
		if quote then 
			while true do
				local ntoken = nextChar()
				if not ntoken then error("incomplete string") end
				if ntoken == quote then return token end
				token = token..ntoken
			end
		end

		return token ~= ""
	end

	while chars[1] do
		local line = chars[1][2] or "?"
		if isWhitespace() then
			nextChar()
		elseif isNumber() then
			tokens[#tokens + 1] = {tonum(token, base), "num", line}
		elseif isIdentifier() then
			tokens[#tokens + 1] = {token, token_exprs[token] and "key" or "id", line}
		elseif isSymbol() then
			tokens[#tokens + 1] = {token, "sym", line}
		elseif isString() then
			tokens[#tokens + 1] = {'"'..token..'"', "str", line}
		else
			error("invalid token @ line " ..line..  ": |" ..tostring(token).. "|")
		end
	end

	return function() position = position + 1; return tokens[position] end
end