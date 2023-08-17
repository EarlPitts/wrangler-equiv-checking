-module(repo).

-export([copy/2,
         get_diff/2,
         checkout/1]).

-spec copy(string(), string()) -> string().
copy(ProjFolder, TmpFolder) ->
    file:make_dir(TmpFolder),
    os:cmd("git clone " ++ ProjFolder ++ " " ++ TmpFolder).

-spec checkout(string()) -> string().
checkout(Hash) ->
    os:cmd("git checkout " ++ Hash).

get_diff(OrigHash, RefacHash) ->
    os:cmd("git diff -U0 --no-ext-diff " ++ OrigHash ++ " " ++ RefacHash).
