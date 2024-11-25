-module(equivchecker_utils).

-compile(export_all).

-include("equivchecker.hrl").

statistics() ->
    % Would be nice to show the total number of tested functions
    [{_, FailCounts}] = ets:lookup(stat, counts),
    Average = lists:sum(FailCounts) / length(FailCounts),
    {FailCounts, Average}.

count_tests("Failed: After ~b test(s).~n", Args) ->
    [{_, Counts}] = ets:lookup(stat, counts),
    ets:insert(stat, {counts, Counts ++ Args});
count_tests(_, _) ->
    ok.

read(FileName) ->
    {ok, F} = file:read_file(FileName),
    erlang:binary_to_list(F).

% Splits up a list containing an even number of items into groups of two
group_by_two([]) -> [];
group_by_two([H1,H2|T]) -> [[H1,H2]|group_by_two(T)].

% Split up arguments passed as a string into a list of the individual arguments
split_args(SpecStr) -> args(SpecStr, "").

args([], Acc) -> [Acc];
args([H|T], _) when [H] =:= "(" and (T =:= ")") -> "";
args([H|T], Acc) when [H] =:= "(" -> paren(T, Acc ++ "(", 0);
args([H|T], Acc) when [H] =:= "{" -> curly(T, "{" ++ Acc, 0);
args([H|T], Acc) when [H] =:= "," -> [Acc|args(T, "")];
args([H|T], Acc) when [H] =:= "[" -> bracket(T, "[" ++ Acc, 0);
args([H|T], Acc) -> args(T, Acc ++ [H]).

paren([H|T], Acc, Level) when [H] =:= "(" -> paren(T, Acc ++ "(", Level + 1);
paren([H|[_|T]], Acc, Level) when ([H] =:= ")") and (Level =:= 0) -> [Acc ++ ")"|args(T, "")];
paren([H|[]], Acc, Level) when ([H] =:= ")") and (Level =:= 0) -> [Acc ++ ")"];
paren([H|T], Acc, Level) when ([H] =:= ")") and (Level =/= 0) -> paren(T, Acc ++ ")", Level - 1);
paren([H|T], Acc, Level) -> paren(T, Acc ++ [H], Level).

curly([H|T], Acc, Level) when [H] =:= "{" -> curly(T, Acc ++ "{", Level + 1);
curly([H|[_|T]], Acc, Level) when ([H] =:= "}") and (Level =:= 0) -> [Acc ++ "}"|args(T, "")];
curly([H|[]], Acc, Level) when ([H] =:= "}") and (Level =:= 0) -> [Acc ++ "}"];
curly([H|T], Acc, Level) when ([H] =:= "}") and (Level =/= 0) -> curly(T, Acc ++ "}", Level - 1);
curly([H|T], Acc, Level) -> curly(T, Acc ++ [H], Level).

bracket([H|T], Acc, Level) when [H] =:= "[" -> bracket(T, Acc ++ "[", Level + 1);
bracket([H|[_|T]], Acc, Level) when ([H] =:= "]") and (Level =:= 0) -> [Acc ++ "]"|args(T, "")];
bracket([H|[]], Acc, Level) when ([H] =:= "]") and (Level =:= 0) -> [Acc ++ "]"];
bracket([H|T], Acc, Level) when ([H] =:= "]") and (Level =/= 0) -> bracket(T, Acc ++ "]", Level - 1);
bracket([H|T], Acc, Level) -> bracket(T, Acc ++ [H], Level).

-spec filename_to_module(string()) -> atom().
filename_to_module(FileName) ->
    erlang:list_to_atom(filename:basename(FileName, ".erl")).

-spec module_to_filename(atom()) -> string().
module_to_filename(Module) ->
    erlang:atom_to_list(Module) ++ ".erl".

% This is a dummy process for suppressing any io message sent to it
% It works by just simply ignoring the message, and sending back an 'ok' reply
% accoring to the I/O protocol (https://www.erlang.org/doc/apps/stdlib/io_protocol.html)
dummy_group_leader() ->
    receive
        {io_request, From, ReplyAs, _} ->
            From ! {io_reply, ReplyAs, ok},
            dummy_group_leader()
    end.

% Disables the output by using the dummy group leader
% Gives back the old group leader, so output could be reenabled later
% by the enable_output/1 function
-spec disable_output() -> pid().
disable_output() ->
    Old = group_leader(),
    New = spawn(equivchecker_utils, dummy_group_leader, []),
    group_leader(New, self()),
    Old.

-spec enable_output(pid()) -> none().
enable_output(Leader) ->
    group_leader(Leader, self()).

% Custom group leader for sending all io_request to specified process
% and ignoring any input
capture_group_leader(Pid) ->
    receive
        {io_request, From, ReplyAs, O} when element(1,O) =:= 'put_chars' ->
            From ! {io_reply, ReplyAs, ok},
            Pid ! {io, O},
            group_leader(self(), self()),
            capture_group_leader(Pid);
        {io_request, From, ReplyAs, _} ->
            From ! {io_reply, ReplyAs, {error, 'input'}},
            capture_group_leader(Pid)
    end.

% Sends the io_request to the given process,
% also errors out on any input
-spec start_capture(pid()) -> {pid()}.
start_capture(Pid) ->
    Old = group_leader(),
    New = spawn(equivchecker_utils, capture_group_leader, [Pid]),
    group_leader(New, self()),
    Old.

-spec stop_capture(pid()) -> none().
stop_capture(Leader) ->
    group_leader(Leader, self()).

-spec common_filename_postfix(filename(), filename()) -> filename().
common_filename_postfix(F1, F2) ->
    filename:join(common_postfix(filename:split(F1),
                                 filename:split(F2))).

-spec common_postfix(list(), list()) -> list().
common_postfix(L1, L2) -> common_postfix(lists:reverse(L1), lists:reverse(L2), []).

-spec common_postfix(list(), list(), list()) -> list().
common_postfix([H1|T1], [H2|T2], Acc) when H1 =:= H2 ->
    common_postfix(T1,T2, [H1|Acc]);
common_postfix(_, _, Acc) -> Acc.

% Removes Dir from the filename File
-spec remove_base_dir(filename(), filename()) -> filename().
remove_base_dir(Dir, File) ->
    DirLen = length(filename:split(Dir)),
    FileList = filename:split(File),
    filename:join(lists:sublist(FileList, DirLen + 1, length(FileList))).

% Traverses a mix of nested lists/tuples and replaces any Pid with the atom 'pid'
remove_pid(List) when is_list(List) ->
  [remove_pid(Item) || Item <- List];
remove_pid(Tuple) when is_tuple(Tuple) ->
  list_to_tuple([remove_pid(Item) || Item <- tuple_to_list(Tuple)]);
remove_pid(Pid) when is_pid(Pid) ->
  pid;
remove_pid(Item) ->
  Item.

log(IsVerbose, Message) ->
    if IsVerbose ->
           io:format(Message ++ "~n", []);
       true -> ok
    end.
log(IsVerbose, Message, Term) ->
    if IsVerbose ->
           io:format(Message, []),
           io:format(": ~p~n", [Term]);
       true -> ok
    end.
