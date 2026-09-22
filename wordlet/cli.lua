-- Command-line entry point. Returns function(api, argv) -> exit status.
local D = require("wordlet.diag")

local USAGE = [[usage: wordlet [--header NAME] [--unit] [--check] [--no-inline] [-o FILE] FILE.let
  --unit        emit one self-contained translation unit (default)
  --header NAME emit a header/source pair; NAME is the header file name
  --check       parse and compile only; report diagnostics without emitting C
  --no-inline   give a private function plain internal linkage instead of forced inlining
  -o FILE       write to FILE instead of stdout]]

return function(api, argv)
    local path, output, headerName, checkOnly = nil, nil, nil, false
    local options = {}
    local index = 1
    while argv[index] do
        local arg = argv[index]
        if arg == "--check" then checkOnly = true
        elseif arg == "--unit" then headerName = nil
        elseif arg == "--no-inline" then options.inline = false
        elseif arg == "--header" then
            index = index + 1
            headerName = argv[index]
            if not headerName then io.stderr:write("wordlet: --header needs a name\n"); return 2 end
        elseif arg == "-o" then
            index = index + 1
            output = argv[index]
            if not output then io.stderr:write("wordlet: -o needs a path\n"); return 2 end
        elseif arg == "-h" or arg == "--help" then
            io.stdout:write(USAGE, "\n")
            return 0
        elseif arg:sub(1, 1) == "-" then
            io.stderr:write("wordlet: unknown option " .. arg .. "\n" .. USAGE .. "\n")
            return 2
        elseif not path then
            path = arg
        else
            io.stderr:write("wordlet: unexpected argument " .. arg .. "\n")
            return 2
        end
        index = index + 1
    end
    if not path then
        io.stderr:write(USAGE, "\n")
        return 2
    end

    local ok, result = pcall(function()
        local artifact = api.compile_file(path, options)
        if checkOnly then return true end
        return artifact
    end)
    if not ok then
        io.stderr:write(D.format(result), "\n")
        return D.status(result)
    end
    if checkOnly then
        io.stdout:write(path .. ": ok\n")
        return 0
    end

    local artifact = result
    local text
    if headerName then
        local sourceName = (output or path:gsub("%.let$", "") .. ".c")
        text = artifact:source(headerName)
        local headerPath = sourceName:gsub("[^/]*$", headerName)
        local headerFile = io.open(headerPath, "wb")
        if not headerFile then
            io.stderr:write("wordlet: cannot write " .. headerPath .. "\n")
            return 1
        end
        headerFile:write(artifact:header((headerName:gsub("%.h$", ""))))
        headerFile:close()
        if not output then
            io.stdout:write(text)
            return 0
        end
    else
        text = artifact:unit()
    end

    if output then
        local file, err = io.open(output, "wb")
        if not file then
            io.stderr:write("wordlet: cannot write " .. output .. ": " .. tostring(err) .. "\n")
            return 1
        end
        file:write(text)
        file:close()
    else
        io.stdout:write(text)
    end
    return 0
end
