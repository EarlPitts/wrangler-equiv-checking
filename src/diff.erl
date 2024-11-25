%% This module is for extracting information from the diff, and presenting it
%% The main unit of the differences between two versions is a hunk, which contains
%% all the information about a change that is needed for finding out what has to be tested
-module(diff).

-include("equivchecker.hrl").

-export([diff/1,
         modified_files/1]).

-type diff_line()   :: string().
-type hunk()        :: {filename(), [diff_line()]}.
-type length()      :: integer().

-spec diff(string()) -> diffs().
diff(DiffStr) ->
    LinesByFiles = parse_diff(DiffStr),
    lists:map(fun({FileName, LineData}) ->
                      {FileName, extract_lines(LineData)} end, LinesByFiles).


extract_lines(LineData) ->
    LineNums = lists:map(fun extract_line/1, LineData),
    {Origs, Refacs} = lists:unzip(LineNums),
    OrigLines = lists:flatmap(fun interval/1, Origs),
    RefacLines = lists:flatmap(fun interval/1, Refacs),
    {OrigLines, RefacLines}.

% Regexp for extracting line numbers of modified lines from hunks
-spec extract_line(string()) -> {{line_num(), length()}, {line_num(), length()}}.
extract_line(LineData) ->
    Options = [{capture, [1,2,3,4], list}],
    Pattern = "@@ -(\\d+),?(\\d?).*\\+(\\d+),?(\\d?).*@@",
    {match, [OrigStart, OrigLen, RefacStart, RefacLen]} = re:run(LineData, Pattern, Options),
    {OS, OL, RS, RL} = line_numbers(OrigStart, OrigLen, RefacStart, RefacLen),
    {{OS, OL}, {RS, RL}}.


-spec line_numbers(line_num(), length(), line_num(), length()) ->
    {line_num(), line_num(), line_num(), line_num()}.
line_numbers(OrigStart, OrigLen, RefacStart, RefacLen) ->
    OS = erlang:list_to_integer(OrigStart),
    RS = erlang:list_to_integer(RefacStart),
    case {OrigLen, RefacLen} of
        {[], []}   -> {OS, 0, RS, 0};
        {[], _}    -> {OS, 0, RS, erlang:list_to_integer(RefacLen)};
        {_, []}    -> {OS, erlang:list_to_integer(OrigLen), RS, 0};
        _          -> {OS, erlang:list_to_integer(OrigLen), RS, erlang:list_to_integer(RefacLen)}
    end.
    
% Given a starting position and a length, gives back the interval [start, start+length]
-spec interval({line_num(), length()}) -> {line_num(), line_num()}.
interval({Start, 0}) ->
    [Start];
interval({Start, Len}) ->
    [Start|interval({Start+1,Len-1})].

-spec modified_files(diffs()) -> [filename()].
modified_files(Diffs) ->
    lists:map(fun({FileName, _}) -> FileName end, Diffs).

% Gets the diff output, and splits it into hunks
-spec parse_diff(string()) -> [hunk()].
parse_diff(DiffStr) ->
    [_|Files] = string:split(DiffStr, "diff -x .git -u0 -br ", all),
    Hunks = lists:map(fun(Str) -> string:split(Str, "\n", all) end, Files),
    ErlangHunks = lists:filter(fun([Header|_]) -> is_erl_source(Header) end, Hunks),
    HunksByFiles = lists:map(fun([H,_,_|T]) -> {extract_file(H), lists:droplast(T)} end, ErlangHunks),
    lists:map(fun({FileName, Lines}) ->
                      {FileName,
                       lists:filter(fun(Line) -> lists:prefix("@@", Line) end, Lines)} end, HunksByFiles).

% Extracts the filenames from the diff output
-spec extract_file(string()) -> filename().
extract_file(DiffLine) ->
    Options = [global, {capture, [1,2], list}],
    {match, [[OrigFile, RefacFile]]} = re:run(DiffLine, ".*?(/.*?\\.erl).*?(/.*?\\.erl)", Options),
    equivchecker_utils:common_filename_postfix(OrigFile, RefacFile).

% Checks if the given file in the diff output is erlang source code
-spec is_erl_source([diff_line()]) -> boolean().
is_erl_source(Header) ->
    case re:run(Header, ".*(.*\\.erl).*") of
        {match,_}   -> true;
        nomatch     -> false
    end.
