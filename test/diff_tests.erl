-module(diff_tests).

-import(diff,
        [extract_file/1, extract_lines/1, parse_diff/1, extract_line/1, extract_file/1]).

-include_lib("eunit/include/eunit.hrl").

diff_output() ->
    equivchecker_utils:read("test_data/diff_output/diff.txt").

diff_files() ->
    equivchecker_utils:read("test_data/diff_output/diff_files.txt").

extract_hunks_right_number_of_files_test() ->
    HunksByFile = parse_diff(diff_output()),
    ?assertEqual(length(HunksByFile), 7).

extract_hunks_right_number_of_hunks_test() ->
    HunksByFile = parse_diff(diff_output()),
    AllHunks = lists:flatmap(fun({_, Hunks}) -> Hunks end, HunksByFile),
    ?assertEqual(length(AllHunks), 95).

extract_hunks_right_number_of_linenums_test() ->
    HunksByFile = parse_diff(diff_output()),
    AllHunks = lists:flatmap(fun({_, Hunks}) -> Hunks end, HunksByFile),
    LineNums = lists:map(fun(Line) -> extract_line(Line) end, AllHunks),
    ?assertEqual(length(LineNums), 95).

extract_filenames_test() ->
    FileNames =
        lists:map(fun(DiffLine) -> extract_file(DiffLine) end,
                  string:split(
                      string:trim(diff_files()), "\n", all)),
    Expected =
        ["/a/test2.erl",
         "/test2.erl",
         "/test3.erl",
         "/test4.erl",
         "/test5.erl",
         "/test6.erl",
         "/test.erl"],
    ?assertEqual(FileNames, Expected).
