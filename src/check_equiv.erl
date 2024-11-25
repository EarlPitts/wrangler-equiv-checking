-module(check_equiv).

-include("equivchecker.hrl").

-compile(export_all). % Exports all functions
-compile(debug_info).

compile(Modules, DirName, Seed) ->
    % TODO Handle error
    file:make_dir(DirName),
    lists:map(fun(X) ->
                      compile:file(X,
                                   [export_all,
                                    debug_info,
                                    {outdir, DirName},
                                    {parse_transform, pt},
                                    {warn_format, 0},
                                    {seed, Seed}
                                   ])
              end, Modules).

% This is a hack, see https://github.com/harp-project/EquivcheckEr/issues/26 for details
unzip_modules() ->
    {ok, [_,_,_,{archive,Archive}]} = escript:extract(escript:script_name(),[]),
    {ok, Files} = zip:unzip(Archive,[memory]),
    {_, Bin} = lists:keyfind("equivchecker/ebin/equivchecker_testing.beam", 1, Files),
    {_, Bin2} = lists:keyfind("equivchecker/ebin/equivchecker_utils.beam", 1, Files),
    file:write_file(filename:join([?ORIGINAL_BIN_FOLDER, "equivchecker_testing.beam"]), Bin),
    file:write_file(filename:join([?REFACTORED_BIN_FOLDER, "equivchecker_testing.beam"]), Bin),
    file:write_file(filename:join([?ORIGINAL_BIN_FOLDER, "equivchecker_utils.beam"]), Bin2),
    file:write_file(filename:join([?REFACTORED_BIN_FOLDER, "equivchecker_utils.beam"]), Bin2).

start_nodes() ->
    % TODO Handle error, use other port if its already used
    {_, Orig, _} = peer:start(#{name => orig, connection => 33001, args => ["-pa", ?ORIGINAL_BIN_FOLDER]}),
    {_, Refac, _} = peer:start(#{name => refac, connection => 33002, args => ["-pa", ?REFACTORED_BIN_FOLDER]}),
    {Orig, Refac}.

stop_nodes(Orig, Refac) ->
    peer:stop(Orig),
    peer:stop(Refac).

% Gets the list of names for changed files based on the diff, and gives back
% the token list and AST for each
-spec read_sources(filename()) -> {filename(), file_info()}.
read_sources(FileName) ->
    Source = equivchecker_utils:read(FileName),
    {_, Tokens, _} = erl_scan:string(Source),
    {ok, AST} = epp_dodger:quick_parse_file(FileName),

    {Tokens, AST}.

get_typeinfo(Dir) ->
    TyperOut = os:cmd("typer -I include -r " ++ Dir),
    typing:types(TyperOut).

check_equiv(OrigDir, RefacDir, IsVerbose) ->
    Configs = config:load_config(),
    equivchecker_utils:log(IsVerbose, "Loaded config", Configs),
    typing:ensure_plt(Configs),

    DiffOutput = os:cmd("diff -x '.git' -u0 -br " ++ OrigDir ++ " " ++ RefacDir),
    Diffs = diff:diff(DiffOutput),
    equivchecker_utils:log(IsVerbose, "Diffs found", Diffs),
    ModFiles = diff:modified_files(Diffs),
    equivchecker_utils:log(IsVerbose, "Modified files", ModFiles),
    % TODO Compile everything for now
    % Files = string:split(string:trim(os:cmd("find -name '*.erl'")), "\n", all),

    FileInfos = lists:map(fun(FileName) ->
                                  {FileName,
                                   read_sources(OrigDir ++ "/" ++ FileName),
                                   read_sources(RefacDir ++ "/" ++ FileName)} end,
                          ModFiles),
    {OrigTypeInfo, RefacTypeInfo} = {get_typeinfo(OrigDir), get_typeinfo(RefacDir)},
    {OrigModFuns, RefacModFuns} = functions:modified_functions(Diffs, FileInfos),
    equivchecker_utils:log(IsVerbose, "Original functions", OrigModFuns),
    equivchecker_utils:log(IsVerbose, "Refactored functions", RefacModFuns),

    CallGraph = functions:callgraph(OrigDir, RefacDir),
    Types = typing:add_types(OrigTypeInfo, RefacTypeInfo),

    % Gets back the functions that have to be tested
    FunsToTest = slicing:scope(OrigModFuns, RefacModFuns, CallGraph, Types),
    equivchecker_utils:log(IsVerbose, "Testing functions", RefacModFuns),

    % Compile the necessary modules into two separate folders
    % This is needed because QuickCheck has to evaluate to old and the new
    % function repeatedly side-by-side

    % TODO Files should contain all the used modules, not just the ones affected by the change
    OrigFiles = lists:map(fun(File) -> filename:join([OrigDir, File]) end, ModFiles),
    RefacFiles = lists:map(fun(File) -> filename:join([RefacDir, File]) end, ModFiles),

    Seed = os:timestamp(), % seed for the PropEr generator
    equivchecker_utils:log(IsVerbose, "Seed used for test generation", Seed),

    compile(OrigFiles, ?ORIGINAL_BIN_FOLDER, Seed),
    compile(RefacFiles, ?REFACTORED_BIN_FOLDER, Seed),

    unzip_modules(),

    {OrigNode, RefacNode} = start_nodes(),
    equivchecker_utils:log(IsVerbose, "Started testing nodes"),

    % This is needed because PropEr needs the source for constructing the generator
    {ok, Dir} = file:get_cwd(),
    file:set_cwd(OrigDir),

    Result = equivchecker_testing:run_tests(FunsToTest, OrigNode, RefacNode, Types, CallGraph, IsVerbose),

    file:set_cwd(Dir),
    stop_nodes(OrigNode, RefacNode),
    equivchecker_utils:log(IsVerbose, "Stopped testing nodes"),
    Result.
