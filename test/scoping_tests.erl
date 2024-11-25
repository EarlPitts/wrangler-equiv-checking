-module(scoping_tests).

-import(scoping,
        [get_name/1,
         get_arity/1,
         is_function_def/1,
         extract_file/1,
         get_module/1]).

-include_lib("eunit/include/eunit.hrl").

-import(equivchecker_utils, [read/1]).
sources() ->
    {ok, Filenames} = file:list_dir("test_data/sources"),
    Paths = lists:map(fun(Filename) -> "test_data/sources/" ++ Filename end, Filenames),
    lists:map(fun equivchecker_utils:read/1, Paths).

specs() ->
    {ok, Filenames} = file:list_dir("test_data/specs"),
    Paths = lists:map(fun(Filename) -> "test_data/specs/" ++ Filename end, Filenames),
    lists:map(fun equivchecker_utils:read/1, Paths).
