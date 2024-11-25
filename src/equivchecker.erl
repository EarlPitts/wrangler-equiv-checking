-module(equivchecker).

%% API exports
-export([main/1]).

%%====================================================================
%% API functions
%%====================================================================

%% escript Entry point
main(Args) ->
    argparse:run(Args, cli(), #{progname => "Equivalence checker"}).

cli() ->
    #{
      arguments => [
                    #{name => target, required => false},
                    #{name => source, required => false},
                    #{name => json, type => boolean, short => $j, long => "-json", default => false},
                    #{name => commit, type => boolean, short => $c, long => "-commit", default => false},
                    #{name => stats, type => boolean, short => $s, long => "-statistics", default => false},
                    #{name => verbose, type => boolean, short => $v, long => "-verbose", default => false}
                   ],
      handler => fun cli:run/1
     }.

%%====================================================================
%% Internal functions
%%====================================================================
