-module(pt).

-export([parse_transform/2]).

parse_transform(Forms, Options) ->
    % io:fwrite("Forms = ~p~n", [Forms]),
    % Forms.
    {seed, Seed} = lists:keyfind(seed, 1, Options),
    Trans = fun (Form) -> do_transform(Seed, Form) end,
    parse_trans:plain_transform(Trans, Forms).


do_transform(_, {'op', L, '!', Lhs, Rhs}) ->
    [NewRhs] = parse_trans:plain_transform(fun transform_send/1, [Rhs]),
    {'op', L, '!', Lhs, NewRhs};
do_transform(Seed, {'receive', _, _} = T) ->
    Trans = fun (Form) -> transform_receive(Seed, Form) end,
    hd(parse_trans:plain_transform(Trans, [T]));
do_transform(_, _) ->
    continue.


% In case of sending a message, what we want is to send a message as is, but also
% to log it somehow (e.g.: we are printing it out in this example)
% Because the RHS of ! doesn't allow sequencing with ',', we have to somehow wrap the
% print statement and the expressin we are sending, so they will be represented by a
% single syntactic unit
% That can be done by just using a block expression
% Pid ! {self(), hello}
% Pid ! begin
%           io:format("~p~n",[{self(), hello}]),
%           {self(), hello}
%       end

transform_send(T) ->
    L = erl_syntax:get_pos(T),
    {block,
    L,
    [{call,
      L,
      {remote,L,{atom,L,io},{atom,L,format}},
      [{string,L,"Sent: ~p~n"},{cons,L,T,{nil,L}}]}, % This is where we log the message
     T % This is the original message
    ]}.

% When receiving messages, we want to first populate the mailbox of the process,
% so reading from it won't block
% We can match on the receive node in the AST, and replace it with a lambda that
% uses PropEr to generate a list of random data (I'm using any for now), then
% send it to itself
% begin
%     {ok, RandomData} = proper_gen:pick(proper_types:list(proper_types:any()), 100),
%     lists:map(fun(X) -> self() ! X end, RandomData),
%     receive
%         {Pid, Msg} ->
%             io:format("~p~n",[Msg])
%     end
% end
%
% Later it would be better to look at the match clasuses inside the receive and generate
% data based on that
transform_receive(Seed, T) ->
    L = erl_syntax:get_pos(T),
    Patterns = extract_receive_clauses(T),
    Generators = [pattern_to_generator(Pattern) || Pattern <- Patterns],
    GeneratorFunctions = generate_random_data(Generators, L, Seed),

    MapFun = erl_syntax:fun_expr([
        erl_syntax:clause([erl_syntax:variable('Function')],
        [],
        [
            erl_syntax:match_expr(
                erl_syntax:tuple([
                    erl_syntax:atom(ok),
                    erl_syntax:variable('Result')
                ]),
                erl_syntax:variable('Function')
            ),
            erl_syntax:variable('Result')
        ])
    ]),

    %% Reverting fixes the location number issue
    RevertedMapFun = erl_syntax:revert(MapFun),

    GeneratorList = erl_syntax:list(GeneratorFunctions),
    RevertedGeneratorList = erl_syntax:revert(GeneratorList),
    
    MapCall = erl_syntax:application(
        erl_syntax:module_qualifier(
            erl_syntax:atom(lists),
            erl_syntax:atom(map)
        ),
        [RevertedMapFun, RevertedGeneratorList]
    ),
    RevertedMapCall = erl_syntax:revert(MapCall),

    SendLC = erl_syntax:list_comp(
        erl_syntax:abstract({op, L, '!',
            {call, L, {atom, L, self}, []},
            {var, L, 'Item'}}),
        [erl_syntax:abstract({generate, L, 
            {var, L, 'Item'}, 
            {var, L, 'RandomData'}})]
    ),
    RevertedSendLC = erl_syntax:revert(SendLC),

    Block = erl_syntax:block_expr([
        erl_syntax:match_expr(
            erl_syntax:variable('RandomData'),
            RevertedMapCall 
        ),
        RevertedSendLC,
        T
    ]),

    RevertedBlock = erl_syntax:revert(Block),

    % Pretty printing the AST before reverting
    % io:format("Generated AST:~n~s~n", [erl_prettypr:format(RevertedBlock)]),

    RevertedBlock.

generate_random_data(Generators, L, Seed) ->
    [begin
        Call = erl_syntax:application(
            erl_syntax:module_qualifier(
                erl_syntax:atom(proper_gen),
                erl_syntax:atom(pick)
            ),
            [
                Generator,
                erl_syntax:integer(100),
                erl_syntax:abstract(Seed)
            ]
        ),
        CallWithPos = erl_syntax_lib:map(
            fun(Node) -> erl_syntax:set_pos(Node, L) end,
            Call
        ),
        erl_syntax:revert(CallWithPos)
    end || Generator <- Generators].

extract_receive_clauses({'receive', _LocationInfo, Clauses}) ->
    PatternList = [ Patterns || {clause, _Location, Patterns, _Guards, _Body} <- Clauses],
    lists:flatten(PatternList);

extract_receive_clauses(_Other) ->
    [].

pattern_to_generator(Pattern) ->
    L = erl_syntax:get_pos(Pattern),
    Generator = case erl_syntax:type(Pattern) of
        tuple ->
            Elements = erl_syntax:tuple_elements(Pattern),
            ElementsGenerators = [pattern_to_generator(Element) || Element <- Elements],
            {call, proper_types, tuple, ElementsGenerators};
        atom ->
            Value = erl_syntax:atom_value(Pattern),
            {call, proper_types, return, [Value]};
        variable ->
            {call, proper_types, any, []};
        integer ->
            {call, proper_types, integer, []};
        string ->
            {call, proper_types, string, []};
        list ->
            Elements = erl_syntax:list_elements(Pattern),
            case Elements of
                [] -> {call, proper_types, list, [{call, proper_types, any, []}]};
                _ -> 
                    ElementsGenerators = [pattern_to_generator(Element) || Element <- Elements],
                    {call, proper_types, list, ElementsGenerators}
            end;
        pid ->
            {call, proper_types, pid, []};
        binary ->
            {call, proper_types, binary, []};
        Type ->
            io:format("Unhandled pattern type: ~p~n", [Type]),
            {call, proper_types, any, []}
    end,
    
    erl_syntax:revert(
        erl_syntax_lib:map(
            fun(Node) -> erl_syntax:set_pos(Node, L) end,
            erl_syntax:abstract(Generator)
        )
    ).

% get_types(Clauses) ->
%     erlang:display(erl_syntax_lib:analyze_form(Clauses)).
% lists:map(fun({_,_,[P],_,_}) -> erlang:display(erl_syntax:type(P)) end, Clauses).
