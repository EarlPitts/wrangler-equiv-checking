-module(equivchecker_testing).

-type type() :: string().

-export([run_tests/6,
         run_tests/7,
         eval_proc/3,
         eval_func/4]).

-define(PEER_TIMEOUT, 1000).

-include_lib("proper/include/proper.hrl").

run_tests(Functions, OrigNode, RefacNode, Types, CallGraph, IsVerbose) ->
    run_tests(Functions, OrigNode, RefacNode, Types, CallGraph, [], IsVerbose).

run_tests([], _, _, _, _, Results, _) ->
    Results;
run_tests(Functions, OrigNode, RefacNode, Types, CallGraph, Results, IsVerbose) ->
    % proper:quickchek/2 stops the server, so it has to be started every time
    proper_typeserver:start(),
    ProperOpts = [long_result, {on_output, fun(X,Y) -> equivchecker_utils:count_tests(X,Y) end}],

    % Convert type information to PropEr type
    FunctionsTyped = lists:map(fun({FileName, {M,F,A}, ArgTypes}) -> {FileName, {M, F, A}, convert_type(FileName, M, ArgTypes)} end, Functions),

    % A result is a tuple: {Module, Function, Counterexample}
    % If no counterexample is found, the third value is 'true' instead
    lists:map(fun(Function) ->
                      spawn(equivchecker_testing, test_function, [Function, OrigNode, RefacNode, ProperOpts, self()])
              end, FunctionsTyped),

    Res = collect_results(length(FunctionsTyped), []),

    FailedFuns = lists:filter(fun({_, _, Eq}) -> Eq =/= true end, Res),
    equivchecker_utils:log(IsVerbose, "Failed functions: ", FailedFuns),

    FailedMFA = lists:map(fun({FileName, {M,F,A}, _}) -> {FileName, {M, F, A}} end, FailedFuns),

    Callers = lists:uniq(lists:flatmap(fun({FileName, {_,F,A}}) -> CallGraph({FileName, F, A}, refactored) end, FailedMFA)),
    equivchecker_utils:log(IsVerbose, "Callers of failed functions: ", Callers),
    CallersTyped = lists:map(fun({FileName, MFA}) -> {FileName, MFA, Types(MFA, refactored)} end, Callers),

    run_tests(CallersTyped, OrigNode, RefacNode, Types, CallGraph, FailedFuns ++ Results, IsVerbose).

collect_results(0, Res) -> Res;
collect_results(Num, Res) ->
    receive
        Val -> collect_results(Num - 1, [Val|Res])
    end.

% -spec eval_func(pid(), atom(), atom(), [term()]) -> {atom(), term()}.
eval_func(M, F, A, Pid) ->
    L = equivchecker_utils:start_capture(Pid),
    RetVal = try erlang:apply(M, F, A) of
                 Val -> {normal, Val}
             catch
                 error:Error -> error
             end,
    Pid ! {self(), RetVal},
    equivchecker_utils:stop_capture(L).

eval_proc(M, F, A) ->
    Pid = spawn(equivchecker_testing, eval_func, [M, F, A, self()]),
    receive
        {Pid, Res} -> Res
    end,
    IO = get_messages(),
    {Res,IO}.

% Collects all the io related messages sent back by the capturing process
get_messages()  -> get_messages([]).
get_messages(L) ->
    receive
        {io, Msg} -> get_messages([Msg|L])
    after
        0 -> L
    end.

% Spawns a process on each node that evaluates the function and
% sends back the result to this process
-spec prop_same_output(pid(), pid(), atom(), atom(), [term()]) -> boolean().
prop_same_output(OrigNode, RefacNode, M, F, A) ->
    {Val1,IO1} = peer:call(OrigNode, equivchecker_testing, eval_proc, [M, F, A], ?PEER_TIMEOUT),
    {Val2,IO2} = peer:call(RefacNode, equivchecker_testing, eval_proc, [M, F, A], ?PEER_TIMEOUT),

    Out1 = {Val1,equivchecker_utils:remove_pid(IO1)},
    Out2 = {Val2,equivchecker_utils:remove_pid(IO2)},

    Out1 =:= Out2.

test_function({FileName, {M,F,A}, Type}, OrigNode, RefacNode, Options, Pid) ->
    Pid ! {FileName, {M,F,A}, proper:quickcheck(?FORALL(Xs, Type, prop_same_output(OrigNode, RefacNode, M, F, Xs)), Options)}.

% Gets a single function and finds the PropEr types for its arguments
% -spec convert_type({mfa(), [type()]}) -> 
  % {atom(), atom(), [proper_types:rich_result(proper_types:fin_type())]}.
convert_type(FileName, M, ArgTypes) ->
    % The proper typeserver searches for the source file in the current directory
    case filename:basename(FileName) =:= FileName of
        true -> lists:map(fun(ArgType) -> get_type({M, ArgType}) end, ArgTypes);
        false -> Dir = filename:dirname(FileName),
                 {ok, CurrDir} = file:get_cwd(),
                 try
                    file:set_cwd(Dir),
                    lists:map(fun(ArgType) -> get_type({M, ArgType}) end, ArgTypes)
                 after
                     file:set_cwd(CurrDir)
                 end
    end.

% Convert type string to PropEr type
-spec get_type({atom(), string()}) ->
    proper_types:rich_result(proper_types:fin_type()).
get_type({Module, TypeStr}) ->
    {_, Type} = proper_typeserver:translate_type({Module, TypeStr}),
    Type.
