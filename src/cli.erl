-module(cli).

-include("equivchecker.hrl").

-export([run/1]).

-spec handler(map()) -> none().
handler(#{target := Target,
          source := Source,
          json := Json,
          commit := Commit,
          stats := Stats,
          verbose := IsVerbose})
    when Commit ->
    commit_to_commit(Source, Target, Json, Stats, IsVerbose);
handler(#{target := Target,
          source := Source,
          json := Json,
          commit := Commit,
          stats := Stats,
          verbose := IsVerbose})
    when not Commit ->
    folder_to_folder(Source, Target, Json, Stats, IsVerbose);
handler(#{target := Target,
          json := Json,
          commit := Commit,
          stats := Stats,
          verbose := IsVerbose})
    when Commit ->
    folder_to_commit(Target, Json, Stats, IsVerbose);
handler(#{target := Target,
          json := Json,
          commit := Commit,
          stats := Stats,
          verbose := IsVerbose})
    when not Commit ->
    folder_to_folder(Target, Json, Stats, IsVerbose);
handler(#{json := Json,
          commit := _,
          stats := Stats,
          verbose := IsVerbose}) ->
    folder_to_commit(Json, Stats, IsVerbose).

-spec commit_to_commit(commit(), commit(), boolean(), boolean(), boolean()) -> none().
commit_to_commit(RefacCommit, OrigCommit, Json, Stats, IsVerbose) ->
    not Json
    andalso io:format("Checking commit ~p against commit ~p~n", [OrigCommit, RefacCommit]),
    {ok, ProjFolder} = file:get_cwd(),
    Original = repo:copy(ProjFolder, ?ORIGINAL_SOURCE_FOLDER),
    repo:checkout(Original, OrigCommit),
    Refactored = repo:copy(ProjFolder, ?REFACTORED_SOURCE_FOLDER),
    repo:checkout(Refactored, RefacCommit),
    run_check(Original, Refactored, Json, Stats, IsVerbose).

-spec folder_to_folder(filename(), filename(), boolean(), boolean(), boolean()) -> none().
folder_to_folder(Refactored, Original, Json, Stats, IsVerbose) ->
    not Json
    andalso io:format("Checking folder ~p against folder ~p~n", [Original, Refactored]),
    run_check(Original, Refactored, Json, Stats, IsVerbose).

-spec folder_to_folder(filename(), boolean(), boolean(), boolean()) -> none().
folder_to_folder(Original, Json, Stats, IsVerbose) ->
    not Json andalso io:format("Checking current folder against ~p~n", [Original]),
    {ok, Refactored} = file:get_cwd(),
    run_check(Original, Refactored, Json, Stats, IsVerbose).

-spec folder_to_commit(commit(), boolean(), boolean(), boolean()) -> none().
folder_to_commit(Commit, Json, Stats, IsVerbose) ->
    not Json andalso io:format("Checking current folder against commit ~p~n", [Commit]),
    {ok, Refactored} = file:get_cwd(),
    Original = repo:copy(Refactored, ?ORIGINAL_SOURCE_FOLDER),
    repo:checkout(Original, Commit),
    run_check(Original, Refactored, Json, Stats, IsVerbose).

-spec folder_to_commit(boolean(), boolean(), boolean()) -> none().
folder_to_commit(Json, Stats, IsVerbose) ->
    not Json andalso io:format("Checking current folder against current commit~n"),
    {ok, Refactored} = file:get_cwd(),
    Commit = repo:current_commit(),
    Original = repo:copy(Refactored, ?ORIGINAL_SOURCE_FOLDER),
    repo:checkout(Original, Commit),
    run_check(Original, Refactored, Json, Stats, IsVerbose).

-spec run_check(filename(), filename(), boolean(), boolean(), boolean()) -> none().
run_check(Original, Refactored, Json, Stats, IsVerbose) ->
    Res = check_equiv:check_equiv(
              filename:absname(Original), filename:absname(Refactored), IsVerbose),
    show_result(Res, Json, Stats).

setup() ->
    % Sets the name of the master node
    os:cmd("epmd"),
    net_kernel:start(master, #{name_domain => shortnames}),

    % These are needed for storing statistics
    ets:new(stat, [named_table, public, set, {keypos, 1}]),
    ets:insert(stat, {counts, []}),

    % Creating temporary folders for the source and bytecode
    file:make_dir(?TEMP_FOLDER),
    file:make_dir(?ORIGINAL_BIN_FOLDER),
    file:make_dir(?REFACTORED_BIN_FOLDER),

    application:start(wrangler).

cleanup() ->
    ets:delete(stat),
    file:del_dir_r(?TEMP_FOLDER), % TODO Handle error
    application:stop(wrangler).

-spec run(map()) -> none().
run(Args) ->
    setup(),
    handler(Args),
    cleanup().

% Second arg turns on json output, third shows statistics
-spec show_result([{filename(), mfa(), [any()]}], boolean(), boolean()) -> none().
show_result(Result, false, false) ->
    Formatted = format_results(Result, false),
    io:format("Results: ~p~n", [Formatted]);
show_result(Result, false, true) ->
    {FailCounts, Average} = equivchecker_utils:statistics(),
    Formatted = format_results(Result, false),
    io:format("Results: ~p~n", [Formatted]),
    io:format("Number of functions that failed: ~p~n", [length(FailCounts)]),
    io:format("Average no. tries before counterexample is found: ~p~n", [Average]);
show_result(Result, true, false) ->
    Formatted = format_results(Result, true),
    io:format("~s\n", [jsone:encode(Formatted, [{indent, 2}, {space, 1}])]);
show_result(Result, true, true) ->
    {FailCounts, Average} = equivchecker_utils:statistics(),
    Stats = #{failed_count => length(FailCounts), average_test_count => Average},
    Output = #{statistics => Stats, results => format_results(Result, true)},
    io:format("~s\n", [jsone:encode(Output, [{indent, 2}, {space, 1}])]).

-spec format_results([{filename(), mfa(), [any()]}], boolean()) -> none().
format_results(Results, Json) ->
    case Json of
        true ->
            lists:map(fun format_json/1, Results);
        false ->
            lists:map(fun format_stdout/1, Results)
    end.

% Default formatting
-spec format_stdout({filename(), mfa(), [any()]}) -> {filename(), mfa(), any()}.
format_stdout({FileName, MFA, [CounterExample]}) ->
    {FileName, MFA, CounterExample}.

% Format the output to json
-spec format_json({filename(), mfa(), [any()]}) -> map().
format_json({FileName, MFA, [CounterExample]}) ->
    #{filename => erlang:list_to_atom(FileName),
      mfa => MFA,
      counterexample => CounterExample}.
