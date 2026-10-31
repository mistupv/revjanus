/*  janus_parser.pl -- concrete syntax of sequential Janus: tokenizer, parser and
    pretty-printer (Figure "Language syntax" of the paper).

    Abstract syntax (Lean constructors of Syntax.lean, in snake_case, same argument
    order):
      program(Main, Procs)          Procs = [proc(Id, Body), ...], possibly []
      assign_var(X, Op, E)          x op= e                         Stmt.assVar
      assign_arr(X, E1, Op, E2)     x[e1] op= e2                    Stmt.assArr
      if_then_else(E1, S1, S2, E2)  if e1 then s1 else s2 fi e2     Stmt.ite
      loop(E1, S1, S2, E2)          from e1 do s1 loop s2 until e2  Stmt.loop
      call(Id), uncall(Id), skip                                    Stmt.call/uncall/skip
      seq(S1, S2)                   s1 s2 (right-nested)            Stmt.seq
      const(N), var(X), arr(X, E), binop(Op, E1, E2)                Expr.const/var/arr/bin

    Concrete syntax conventions (see README.md):
      * a program is a statement sequence (the main body) followed by zero or more
        sections "procedure id S";
      * statements are separated by juxtaposition only; a sequence ends at else, fi,
        loop, until, procedure or end of file; empty sequences are not allowed;
      * binary operators, lowest to highest precedence, all left-associative:
            ||   &&   |   ^   &   (= !=)   (< > <= >=)   (+ -)   (* / %)
      * equality is written "=" (as in Figure 1); "==" is rejected with an explicit
        syntax error;
      * a "-" written immediately before digits, in operand position, is a negative
        literal: "x - -1" and "x -1" are x - (-1) and x - 1; there is no unary minus;
      * integer literals must lie in [-2147483648, 2147483647] (Figure 1);
      * identifiers are [A-Za-z_][A-Za-z0-9_]* except the keywords; "//" starts a
        comment that extends to the end of the line.

    Errors are reported by throwing janus_syntax_error(Line, Message).
*/

:- module(janus_parser,
          [ parse_program/2,        % +Source, -Program
            parse_file/2,           % +File, -Program
            tokenize/2,             % +Codes, -Tokens
            pp_program/1,           % +Program
            pp_program_string/2,    % +Program, -String
            pp_stmt/2,              % +Indent, +Stmt
            pp_expr/1,              % +Expr
            binop_symbol/2,         % ?Op, ?Token   e.g. binop_symbol(rem, '%')
            assign_symbol/2,        % ?Op, ?Token   e.g. assign_symbol(add, '+=')
            syntax_error_message/2  % +Error, -String
          ]).

:- use_module(library(lists)).
:- use_module(library(apply)).

% ======================================================================================
% Entry points
% ======================================================================================

%!  parse_program(+Source, -Program) is det.
%   Source is a string, an atom or a code list. Throws janus_syntax_error(Line, Msg).
parse_program(Source, Program) :-
    source_codes(Source, Codes),
    tokenize(Codes, Tokens),
    program(Tokens, Program).

%!  parse_file(+File, -Program) is det.
parse_file(File, Program) :-
    read_file_to_codes(File, Codes, []),
    parse_program(Codes, Program).

source_codes(Source, Codes) :-
    (   is_list(Source)
    ->  Codes = Source
    ;   string(Source)
    ->  string_codes(Source, Codes)
    ;   atom(Source)
    ->  atom_codes(Source, Codes)
    ;   throw(error(type_error(text, Source), parse_program/2))
    ).

%!  syntax_error_message(+Error, -Message) is semidet.
syntax_error_message(janus_syntax_error(Line, Msg), Message) :-
    format(string(Message), "syntax error at line ~w: ~w", [Line, Msg]).

syntax_error(Line, Fmt, Args) :-
    format(string(Msg), Fmt, Args),
    throw(janus_syntax_error(Line, Msg)).

% ======================================================================================
% Tokenizer
% ======================================================================================
%
% Tokens are t(Token, Line) with Token one of
%   int(N, Glue)  N >= 0; Glue = glued if the digits immediately follow a "-"
%   id(Name)      identifier (atom)
%   kw(K)         keyword
%   op(Atom)      operator or punctuation
% and the list ends with t(eof, Line).

keyword(if). keyword(then). keyword(else). keyword(fi).
keyword(from). keyword(do). keyword(loop). keyword(until).
keyword(call). keyword(uncall). keyword(skip). keyword(procedure).

%!  tokenize(+Codes, -Tokens) is det.
tokenize(Codes, Tokens) :-
    tokens(Codes, 1, Tokens).

tokens([], Line, [t(eof, Line)]).
tokens([C|Cs], Line, Ts) :-
    (   C =:= 0'\n
    ->  Line1 is Line + 1,
        tokens(Cs, Line1, Ts)
    ;   code_type(C, space)
    ->  tokens(Cs, Line, Ts)
    ;   C =:= 0'/, Cs = [0'/|_]
    ->  skip_comment(Cs, Rest),
        tokens(Rest, Line, Ts)
    ;   code_type(C, digit)
    ->  digits([C|Cs], Ds, Rest),
        number_codes(N, Ds),
        Ts = [t(int(N, free), Line)|Ts1],
        tokens(Rest, Line, Ts1)
    ;   ident_start(C)
    ->  ident_rest(Cs, IdCs, Rest),
        atom_codes(A, [C|IdCs]),
        (   keyword(A)
        ->  Tok = kw(A)
        ;   Tok = id(A)
        ),
        Ts = [t(Tok, Line)|Ts1],
        tokens(Rest, Line, Ts1)
    ;   C =:= 0'-, Cs = [D|_], code_type(D, digit)
    ->  digits(Cs, Ds, Rest),
        number_codes(N, Ds),
        Ts = [t(op(-), Line), t(int(N, glued), Line)|Ts1],
        tokens(Rest, Line, Ts1)
    ;   C =:= 0'=, Cs = [0'=|_]
    ->  syntax_error(Line, "'==' is not Janus syntax: equality is written '='", [])
    ;   operator([C|Cs], Op, Rest)
    ->  Ts = [t(op(Op), Line)|Ts1],
        tokens(Rest, Line, Ts1)
    ;   syntax_error(Line, "unexpected character '~c'", [C])
    ).

skip_comment([], []).
skip_comment([C|Cs], Rest) :-
    (   C =:= 0'\n
    ->  Rest = [C|Cs]
    ;   skip_comment(Cs, Rest)
    ).

digits([C|Cs], [C|Ds], Rest) :-
    code_type(C, digit), !,
    digits(Cs, Ds, Rest).
digits(Cs, [], Cs).

ident_start(C) :- code_type(C, alpha), C =\= 0'$ ; C =:= 0'_ .
ident_char(C)  :- code_type(C, alnum), C =\= 0'$ ; C =:= 0'_ .

ident_rest([C|Cs], [C|Is], Rest) :-
    ident_char(C), !,
    ident_rest(Cs, Is, Rest).
ident_rest(Cs, [], Cs).

% Longest match first.
operator([0'+, 0'=|R], '+=', R).
operator([0'-, 0'=|R], '-=', R).
operator([0'^, 0'=|R], '^=', R).
operator([0'&, 0'&|R], '&&', R).
operator([0'|, 0'||R], '||', R).
operator([0'!, 0'=|R], '!=', R).
operator([0'<, 0'=|R], '<=', R).
operator([0'>, 0'=|R], '>=', R).
operator([C|R], Op, R) :-
    single_operator(C, Op).

single_operator(0'+, +).  single_operator(0'-, -).  single_operator(0'^, ^).
single_operator(0'*, *).  single_operator(0'/, /).  single_operator(0'%, '%').
single_operator(0'&, &).  single_operator(0'|, '|'). single_operator(0'<, <).
single_operator(0'>, >).  single_operator(0'=, =).  single_operator(0'(, '(').
single_operator(0'), ')'). single_operator(0'[, '['). single_operator(0'], ']').

% ======================================================================================
% Parser (recursive descent, deterministic: the next token always decides)
% ======================================================================================

program(Ts0, program(Main, Procs)) :-
    seq(Ts0, Main, Ts1),
    procedures(Ts1, Procs).

procedures([t(eof, _)], []) :- !.
procedures([t(kw(procedure), _)|Ts0], [proc(Id, Body)|Procs]) :- !,
    identifier(Ts0, Id, Ts1),
    seq(Ts1, Body, Ts2),
    procedures(Ts2, Procs).
procedures([t(T, Line)|_], _) :-
    describe(T, D),
    syntax_error(Line, "expected 'procedure' or end of file, found ~w", [D]).

% A statement sequence: one or more statements, right-nested with seq/2.
seq(Ts0, S, Ts) :-
    Ts0 = [t(T, Line)|_],
    (   ends_sequence(T)
    ->  describe(T, D),
        syntax_error(Line, "empty statement sequence before ~w (use skip)", [D])
    ;   statement(Ts0, S1, Ts1),
        Ts1 = [t(T1, _)|_],
        (   ends_sequence(T1)
        ->  S = S1, Ts = Ts1
        ;   S = seq(S1, S2),
            seq(Ts1, S2, Ts)
        )
    ).

ends_sequence(kw(else)).
ends_sequence(kw(fi)).
ends_sequence(kw(loop)).
ends_sequence(kw(until)).
ends_sequence(kw(procedure)).
ends_sequence(eof).

statement([t(id(X), _)|Ts0], S, Ts) :- !,
    (   Ts0 = [t(op('['), _)|Ts1]
    ->  expr(Ts1, E1, Ts2),
        expect(op(']'), Ts2, Ts3),
        assign_operator(Ts3, Op, Ts4),
        expr(Ts4, E2, Ts),
        S = assign_arr(X, E1, Op, E2)
    ;   assign_operator(Ts0, Op, Ts1),
        expr(Ts1, E, Ts),
        S = assign_var(X, Op, E)
    ).
statement([t(kw(if), _)|Ts0], if_then_else(E1, S1, S2, E2), Ts) :- !,
    expr(Ts0, E1, Ts1),
    expect(kw(then), Ts1, Ts2),
    seq(Ts2, S1, Ts3),
    expect(kw(else), Ts3, Ts4),
    seq(Ts4, S2, Ts5),
    expect(kw(fi), Ts5, Ts6),
    expr(Ts6, E2, Ts).
statement([t(kw(from), _)|Ts0], loop(E1, S1, S2, E2), Ts) :- !,
    expr(Ts0, E1, Ts1),
    expect(kw(do), Ts1, Ts2),
    seq(Ts2, S1, Ts3),
    expect(kw(loop), Ts3, Ts4),
    seq(Ts4, S2, Ts5),
    expect(kw(until), Ts5, Ts6),
    expr(Ts6, E2, Ts).
statement([t(kw(call), _)|Ts0], call(Id), Ts) :- !,
    identifier(Ts0, Id, Ts).
statement([t(kw(uncall), _)|Ts0], uncall(Id), Ts) :- !,
    identifier(Ts0, Id, Ts).
statement([t(kw(skip), _)|Ts], skip, Ts) :- !.
statement([t(T, Line)|_], _, _) :-
    describe(T, D),
    syntax_error(Line, "expected a statement, found ~w", [D]).

assign_operator([t(op(O), _)|Ts], Op, Ts) :-
    assign_token(O, Op), !.
assign_operator([t(T, Line)|_], _, _) :-
    describe(T, D),
    syntax_error(Line, "expected '+=', '-=' or '^=', found ~w", [D]).

assign_token('+=', add).
assign_token('-=', sub).
assign_token('^=', xor).

identifier([t(id(X), _)|Ts], X, Ts) :- !.
identifier([t(T, Line)|_], _, _) :-
    describe(T, D),
    syntax_error(Line, "expected an identifier, found ~w", [D]).

expect(Tok, [t(Tok, _)|Ts], Ts) :- !.
expect(Tok, [t(T, Line)|_], _) :-
    describe(Tok, Expected),
    describe(T, Found),
    syntax_error(Line, "expected ~w, found ~w", [Expected, Found]).

% --- expressions: precedence climbing, all levels left-associative ---------------------

% binop_token(Token, Level, Op): level 1 is the lowest precedence.
binop_token('||', 1, lor).
binop_token('&&', 2, land).
binop_token('|',  3, bor).
binop_token(^,    4, xor).
binop_token(&,    5, band).
binop_token(=,    6, eq).
binop_token('!=', 6, ne).
binop_token(<,    7, lt).
binop_token(>,    7, gt).
binop_token('<=', 7, le).
binop_token('>=', 7, ge).
binop_token(+,    8, add).
binop_token(-,    8, sub).
binop_token(*,    9, mul).
binop_token(/,    9, div).
binop_token('%',  9, rem).

max_level(9).

expr(Ts0, E, Ts) :- expr_level(1, Ts0, E, Ts).

expr_level(L, Ts0, E, Ts) :-
    max_level(Max),
    (   L > Max
    ->  primary(Ts0, E, Ts)
    ;   L1 is L + 1,
        expr_level(L1, Ts0, Left, Ts1),
        expr_rest(L, Left, Ts1, E, Ts)
    ).

expr_rest(L, Left, Ts0, E, Ts) :-
    (   Ts0 = [t(op(O), _)|Ts1],
        binop_token(O, L, Op)
    ->  L1 is L + 1,
        expr_level(L1, Ts1, Right, Ts2),
        expr_rest(L, binop(Op, Left, Right), Ts2, E, Ts)
    ;   E = Left, Ts = Ts0
    ).

primary([t(int(N, _), Line)|Ts], const(N), Ts) :- !,
    check_range(N, Line).
primary([t(op(-), _), t(int(N, glued), Line)|Ts], const(M), Ts) :- !,
    M is -N,
    check_range(M, Line).
primary([t(id(X), _), t(op('['), _)|Ts0], arr(X, E), Ts) :- !,
    expr(Ts0, E, Ts1),
    expect(op(']'), Ts1, Ts).
primary([t(id(X), _)|Ts], var(X), Ts) :- !.
primary([t(op('('), _)|Ts0], E, Ts) :- !,
    expr(Ts0, E, Ts1),
    expect(op(')'), Ts1, Ts).
primary([t(T, Line)|_], _, _) :-
    describe(T, D),
    syntax_error(Line, "expected an expression, found ~w", [D]).

check_range(N, Line) :-
    (   N >= -2147483648, N =< 2147483647
    ->  true
    ;   syntax_error(Line, "integer literal ~w out of range [-2147483648, 2147483647]", [N])
    ).

describe(eof, "end of file") :- !.
describe(kw(K), D) :- !, format(string(D), "'~w'", [K]).
describe(op(O), D) :- !, format(string(D), "'~w'", [O]).
describe(id(X), D) :- !, format(string(D), "identifier '~w'", [X]).
describe(int(N, _), D) :- !, format(string(D), "number ~w", [N]).
describe(T, D) :- format(string(D), "~w", [T]).

% ======================================================================================
% Pretty-printer (its output parses back to the same term)
% ======================================================================================

%!  pp_program(+Program) is det.
pp_program(program(Main, Procs)) :-
    pp_stmt(0, Main),
    forall(member(proc(Id, Body), Procs),
           ( format("procedure ~w~n", [Id]),
             pp_stmt(2, Body) )).

%!  pp_program_string(+Program, -String) is det.
pp_program_string(Program, String) :-
    with_output_to(string(String), pp_program(Program)).

%!  pp_stmt(+Indent, +Stmt) is det.
%   Prints a statement (sequences one statement per line).
pp_stmt(I, seq(S1, S2)) :- !,
    pp_stmt(I, S1),
    pp_stmt(I, S2).
pp_stmt(I, assign_var(X, Op, E)) :- !,
    assign_token(T, Op),
    indent(I), format("~w ~w ", [X, T]), pp_expr(E), nl.
pp_stmt(I, assign_arr(X, E1, Op, E2)) :- !,
    assign_token(T, Op),
    indent(I), format("~w[", [X]), pp_expr(E1), format("] ~w ", [T]), pp_expr(E2), nl.
pp_stmt(I, if_then_else(E1, S1, S2, E2)) :- !,
    I2 is I + 2,
    indent(I), write('if '), pp_expr(E1), write(' then'), nl,
    pp_stmt(I2, S1),
    indent(I), write(else), nl,
    pp_stmt(I2, S2),
    indent(I), write('fi '), pp_expr(E2), nl.
pp_stmt(I, loop(E1, S1, S2, E2)) :- !,
    I2 is I + 2,
    indent(I), write('from '), pp_expr(E1), write(' do'), nl,
    pp_stmt(I2, S1),
    indent(I), write(loop), nl,
    pp_stmt(I2, S2),
    indent(I), write('until '), pp_expr(E2), nl.
pp_stmt(I, call(Id))   :- !, indent(I), format("call ~w~n", [Id]).
pp_stmt(I, uncall(Id)) :- !, indent(I), format("uncall ~w~n", [Id]).
pp_stmt(I, skip)       :- indent(I), write(skip), nl.

indent(I) :- forall(between(1, I, _), put_char(' ')).

%!  pp_expr(+Expr) is det.
%   Minimal parentheses: a left operand needs parentheses if its level is lower than the
%   operator's level, a right operand if it is lower or equal (left associativity).
pp_expr(E) :- pp_expr(E, 1).

pp_expr(const(N), _) :- !, write(N).
pp_expr(var(X), _) :- !, write(X).
pp_expr(arr(X, E), _) :- !, format("~w[", [X]), pp_expr(E, 1), write(']').
pp_expr(binop(Op, E1, E2), Ctx) :-
    print_token(Op, T, L),
    L1 is L + 1,
    (   L < Ctx
    ->  write('('), pp_expr(E1, L), format(" ~w ", [T]), pp_expr(E2, L1), write(')')
    ;   pp_expr(E1, L), format(" ~w ", [T]), pp_expr(E2, L1)
    ).

% The token printed for each operator.
print_token(Op, T, L) :-
    binop_token(T, L, Op), !.

%!  binop_symbol(?Op, ?Token) is semidet.
%   The concrete symbol of a binary operator.
binop_symbol(Op, T) :- binop_token(T, _, Op).

%!  assign_symbol(?Op, ?Token) is semidet.
%   The concrete symbol of an update operator.
assign_symbol(Op, T) :- assign_token(T, Op).
