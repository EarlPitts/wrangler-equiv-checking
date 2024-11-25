-module(functions).

-include("equivchecker.hrl").

-export([modified_functions/2,
        callgraph/2]).

-type fun_name()    :: string().
-type boundaries()  :: {line_num(), line_num()}.

% Finds all the functions in the AST, and pairs them up with their first and last line in the source
-spec functions(tokens(), ast()) -> [{fun_name(), arity(), boundaries()}].
functions(Tokens, AST) ->
    Functions = lists:filter(fun(Tree) -> erl_syntax:type(Tree) =:= function end, AST),
    StartLines = lists:map(fun(Tree) -> erl_syntax:get_pos(leftmost_node(Tree)) end, Functions),
    RightmostLines = lists:map(fun(Tree) -> erl_syntax:get_pos(rightmost_node(Tree)) end, Functions),
    EndLines = lists:map(fun(EndLine) -> offset(EndLine, Tokens) end, RightmostLines),
    Names = lists:map(fun(Tree) -> erl_syntax:atom_value(erl_syntax:function_name(Tree)) end, Functions),
    Arities = lists:map(fun erl_syntax:function_arity/1, Functions),
    lists:zip3(Names, Arities, lists:zip(StartLines, EndLines)).


-spec rightmost_node(ast()) -> ast().
rightmost_node(Tree) ->
    case erlang:is_list(Tree) of
        true -> rightmost_node(lists:last(Tree));
        false ->
            Children = erl_syntax:subtrees(Tree),
            case lists:reverse(Children) of
                [] -> Tree;
                [RightmostChild | _] ->
                    case RightmostChild of
                        [] -> Tree;
                        _  -> rightmost_node(RightmostChild)
                    end
            end
    end.

-spec leftmost_node(ast()) -> ast().
leftmost_node(Tree) ->
    case erlang:is_list(Tree) of
        true -> leftmost_node(hd(Tree));
        false ->
            Children = erl_syntax:subtrees(Tree),
            case Children of
                [] -> Tree;
                [LeftMostChild | _] -> leftmost_node(LeftMostChild)
            end
    end.

% Finds the number of lines after the last meaningful node in the AST
% This is needed because we want the last line of the function based on the
% source file, not from the AST, which doesn't deal with dots and other "unnecessary"
% syntactic elements
-spec offset(line_num(), tokens()) -> line_num().
offset(LineNum, Tokens) ->
    Rest = lists:dropwhile(fun(T) -> erl_scan:line(T) =/= LineNum end, Tokens),
    % We use dot as the last token from the function
    {value, EndToken} = lists:search(fun(T) -> erl_scan:symbol(T) =:= dot end, Rest),
    erl_scan:line(EndToken).

% Finds all the modified functions
-spec modified_functions(diffs(), [{filename(), file_info(), file_info()}]) ->
    {[mfa()], [mfa()]}.
modified_functions(Diffs, FileInfos) ->
    ChangesByFile = lists:map(fun({FileName, OrigInfo, RefacInfo}) ->
                                      {_, LineNums} = lists:keyfind(FileName, 1, Diffs),
                                      {FileName, LineNums, OrigInfo, RefacInfo} end, FileInfos),
    {OrigChanged, RefacChanged} = lists:unzip(lists:map(fun modified/1, ChangesByFile)),
    OrigCombined = lists:concat(OrigChanged),
    RefacCombined = lists:concat(RefacChanged),
    {OrigCombined, RefacCombined}.

% Finds the modified functions for a single file
-spec modified({filename(), boundaries(), file_info(), file_info()}) ->
    {[{filename(), mfa()}], [{filename(), mfa()}]}.
modified({FileName, {OrigLineNums, RefacLineNums},
      {OrigTokens, OrigAST},
      {RefacTokens, RefacAST}}) ->
    OrigFuns = functions(OrigTokens, OrigAST),
    RefacFuns = functions(RefacTokens, RefacAST),
    Module = equivchecker_utils:filename_to_module(FileName),
    OrigChanged = lists:map(fun({Name, Arity, _}) -> {FileName, {Module, Name, Arity}} end, changed(OrigLineNums, OrigFuns)),
    RefacChanged = lists:map(fun({Name, Arity, _}) -> {FileName, {Module, Name, Arity}} end, changed(RefacLineNums, RefacFuns)),
    {OrigChanged, RefacChanged}.

% Predicate for deciding if given line is inside the given function boundaries
-spec inside(boundaries(), line_num()) -> boolean().
inside({Start, End}, Line) ->
    Line >= Start andalso Line =< End.


% Filters out those functions that were affected by the change
-spec changed([line_num()], {fun_name(), arity(), boundaries()}) -> {fun_name(), arity(), boundaries()}.
changed(LineNums, Funs) ->
    lists:filter(fun({_, _, Boundaries}) ->
                         % If any modified line falls inside the function's boundaries, we consider it modified
                         lists:any(fun(Line) -> inside(Boundaries, Line) end, LineNums)
                 end,
                 Funs).

% Returns a closure for getting the callers, based on the version
-spec callgraph(string(), string()) -> fun().
callgraph(OrigDir, RefacDir) ->
    fun(MFA, Version) ->
            case Version of
                original -> find_callers(MFA, OrigDir);
                refactored -> find_callers(MFA, RefacDir)
            end
    end.

-spec find_callers({filename(), atom(), arity()}, string()) -> [{filename(), mfa()}].
find_callers({FileName, FunName, Arity}, Dir) ->
    AbsDir = filename:absname(Dir),
    AbsFileName = AbsDir ++ "/" ++ FileName,
    Leader = equivchecker_utils:disable_output(),
    {_, Funs} = wrangler_code_inspector_lib:calls_to_fun_1(AbsFileName, FunName, Arity, [AbsDir], 4),
    equivchecker_utils:enable_output(Leader),
    lists:map(fun({{FileName, F, A}, _}) ->
                      {equivchecker_utils:remove_base_dir(Dir, FileName), {equivchecker_utils:filename_to_module(FileName), F, A}} end, Funs).
