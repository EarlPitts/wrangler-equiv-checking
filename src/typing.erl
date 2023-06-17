%% The purpose of this module is to generate type information using Typer,
%% and provide an interface for querying this information
-module(typing).

-type type()        :: string().
-type type_info()   :: [{module(), [{string(), arity()}]}].

-export([types/1,
         get_type/2,
         add_types/2,
         ensure_plt/1]).

-include("dialyzer.hrl").

%% Wrapper for parse_typer
-spec types(string()) -> [{module(), [{string(), arity()}]}] | atom().
types(TyperOutput) ->
    parse_typer(TyperOutput).

%% Returns the list of the types of the arguments
-spec get_type(mfa(), type_info()) -> [type()].
get_type({M,F,A}, TypeInfo) ->
    % TODO Get rid of the nested case blocks
    case lists:keyfind(M, 1, TypeInfo) of
        {_, ModuleTypes} -> case lists:keyfind(F, 1, lists:filter(fun({_, Args}) -> length(Args) =:= A end, ModuleTypes)) of
                                false -> lists:duplicate(A, "any()"); % If the type is not found, use any()
                                {_, T} -> T
                            end;
        false            -> lists:duplicate(A, "any()") % If the type is not found, use any()
    end.

%% Given a list of functions and type info, return a new list with the types added
-spec add_types([mfa()], type_info()) -> [{mfa(), [type()]}].
add_types(Funs, TypeInfo) ->
    lists:map(fun(Fun) -> {Fun, get_type(Fun, TypeInfo)} end, Funs).

% Parses the output of typer into a list of tuples in the form of {Filename, [Spec lines]}
-spec parse_typer(string()) -> [{module(), [{string(), arity()}]}] | atom().
parse_typer(TyperOutput) ->
    case re:run(TyperOutput, ".*failed.*\n") of
        {match, _} -> typer_error; % TODO Why does this match `nomatch`???
        _Otherwise ->
            Files = string:split(string:trim(TyperOutput), "\n\n", all),

            Options = [global, {capture, [1,2], list}, dotall],
            Matches = lists:map(fun(FileSpecs) ->
                                re:run(FileSpecs, ".*File: \"./(.*?)\"\n.*---\n(.*)", Options) end, Files),
            Specs = lists:map(fun({_, [[File , Specs]]}) ->
                                {File, Specs} end, Matches),

            lists:map(fun({File, SpecLines}) ->
                            {utils:filename_to_module(File),
                             lists:map(fun parse_spec/1, string:split(SpecLines, "\n", all))} end,
                      Specs)
    end.

% Given a function spec, gives back the name and input types
-spec parse_spec(string()) -> {string(), [string()]}.
parse_spec(SpecStr) ->
    Options = [global, {capture, [1,2], list}],
    {match, [[FunName, ArgsStr]]} = re:run(SpecStr, "-spec (.*?)\\((.*)\\) ->.*", Options),
    
    case ArgsStr of
        []   -> {FunName, ""}; % Nullary function
        Args -> {FunName, utils:split_args(Args)}
    end.

% PLT (Persistent Lookup Table) related functions

prompt_for_plt() ->
    io:format("PLT not found!~n"),
    io:format("Either provide a valid location for an already existing PLT,~n"),
    io:format("or press enter to generate it!~n"),
    io:get_line("> ").

-spec check_plt() -> atom().
check_plt() ->
    Loc = dialyzer_iplt:get_default_iplt_filename(),
    case dialyzer:plt_info(Loc) of
        {ok,_}     -> found;
        _          -> not_found
    end.

-spec ensure_plt(config:config()) -> none().
ensure_plt(Configs) ->
    case config:lookup(Configs, "custom_plt_location") of
        false     -> ok;
        CustomLoc -> os:putenv("DIALYZER_PLT", string:trim(CustomLoc))
    end,
    case check_plt() of
        found     -> ok;
        not_found ->
            case prompt_for_plt() of
                "\n" -> 
                    io:format("Generating PLT. This could take a while...\n"),
                    Apps = ["erts", "kernel", "stdlib", "mnesia"],
                    Dirs = dialyzer_cl_parse:get_lib_dir(Apps),
                    dialyzer_cl:start(#options{analysis_type = plt_build, files = Dirs, get_warnings = false}),
                    ok;
                Loc  ->
                    os:putenv("DIALYZER_PLT", string:trim(Loc)),
                    NewConfig = config:update_config(Configs, "custom_plt_location", Loc),
                    ensure_plt(NewConfig)
            end
    end,
    config:save_config(Configs).
