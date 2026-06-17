% Command-line argument helpers for MeTTa scripts.

get_cmdline_args(Args) :-
    current_prolog_flag(argv, RawArgs),
    ( RawArgs = [_File|Rest] -> Args = Rest ; Args = [] ).

get_cmdline_arg(Index, Arg) :-
    get_cmdline_args(Args),
    ( nth0(Index, Args, A)
    -> Arg = A
    ;  Arg = 'Empty'
    ).

cmdline_arg_count(Count) :-
    get_cmdline_args(Args),
    length(Args, Count).

has_cmdline_args(true) :-
    get_cmdline_args(Args),
    Args \= [], !.
has_cmdline_args(false).
