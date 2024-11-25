-module(typing_tests).

-import(typing,
        [get_specs/1,
         get_args/3,
         parse_spec/1]).

-include_lib("eunit/include/eunit.hrl").

valid_specs() ->
    ["-spec p() -> integer().",
     "-spec q(list(integer())) -> integer().",
     "-spec r(integer(),string()) -> integer()."
    ].

expected_specs() ->
    [
     {p, []},
     {q, ["list(integer())"]},
     {r, ["integer()", "string()"]}
    ].

parse_spec_test() ->
    ?assertEqual(expected_specs(), lists:map(fun typing:parse_spec/1, valid_specs())).
