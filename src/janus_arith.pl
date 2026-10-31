/*  janus_arith.pl -- interpretation of the operators of Janus

    Arithmetic follows the default behaviour of the Jana interpreter, as decided by the
    authors (Section 2 of the paper):

      * values are unbounded integers (SWI-Prolog integers are unbounded);
      * "/" is floor division and "%" the corresponding modulus, i.e.
            a = (a/b)*b + a%b   and   a%b has the sign of b
        which are exactly SWI-Prolog's `div` and `mod`;
      * "/" and "%" by 0 have no value: the predicate FAILS (no derivation) and the
        divisor is tested BEFORE `div`/`mod` is evaluated, so nothing is ever thrown;
      * "&", "|", "^" are bitwise on the two's complement representation
        (SWI-Prolog `/\`, `\/`, `xor`, which use infinite sign extension);
      * comparisons and the logical operators "&&", "||" return 1 (true) or 0 (false);
        "&&" and "||" test whether their operands are nonzero; both operands of every
        binary operator are always evaluated (see eval_expr/3, rule Bop).

    Operator atoms are the Lean constructor names in snake_case (Syntax.lean):
      update operators (ModOp):  add sub xor
      binary operators (BinOp):  add sub xor mul div rem band land lor bor
                                 lt gt eq ne le ge
    In Lean the three update operators are wrapped as `BinOp.mod op`; here they are
    flattened into the 16 binary operator atoms.
*/

:- module(janus_arith,
          [ apply_binop/4,          % +Op, +V1, +V2, -V
            apply_assign_op/4,      % +Op, +A, +V, -R
            inverse_assign_op/2,    % ?Op, ?InvOp
            is_true/1,              % +V
            is_false/1,             % +V
            binop/1,                % ?Op   (the 16 binary operators)
            assign_op/1             % ?Op   (the 3 update operators)
          ]).

%!  assign_op(?Op) is nondet.
%   The update operators of Figure 1: + - ^ .
assign_op(add).
assign_op(sub).
assign_op(xor).

%!  binop(?Op) is nondet.
%   The 16 binary operators of Figure 1.
binop(add).  binop(sub).  binop(xor).
binop(mul).  binop(div).  binop(rem).
binop(band). binop(land). binop(lor).  binop(bor).
binop(lt).   binop(gt).   binop(eq).   binop(ne).   binop(le).   binop(ge).

%!  apply_assign_op(+Op, +A, +V, -R) is det.
%   R = [[Op]](A, V) for an update operator (Lean: ModOp.interp).
apply_assign_op(add, A, V, R) :- R is A + V.
apply_assign_op(sub, A, V, R) :- R is A - V.
apply_assign_op(xor, A, V, R) :- R is A xor V.

%!  inverse_assign_op(?Op, ?InvOp) is det.
%   I_op of Figure 4 (Lean: ModOp.invert).
inverse_assign_op(add, sub).
inverse_assign_op(sub, add).
inverse_assign_op(xor, xor).

%!  apply_binop(+Op, +V1, +V2, -V) is semidet.
%   V = [[Op]](V1, V2) (Lean: BinOp.interp). Fails for "/" and "%" by zero.
apply_binop(add,  V1, V2, V) :- apply_assign_op(add, V1, V2, V).
apply_binop(sub,  V1, V2, V) :- apply_assign_op(sub, V1, V2, V).
apply_binop(xor,  V1, V2, V) :- apply_assign_op(xor, V1, V2, V).
apply_binop(mul,  V1, V2, V) :- V is V1 * V2.
apply_binop(div,  V1, V2, V) :- V2 =\= 0, V is V1 div V2.
apply_binop(rem,  V1, V2, V) :- V2 =\= 0, V is V1 mod V2.
apply_binop(band, V1, V2, V) :- V is V1 /\ V2.
apply_binop(land, V1, V2, V) :- bool_value((is_true(V1), is_true(V2)), V).
apply_binop(lor,  V1, V2, V) :- bool_value((is_true(V1) ; is_true(V2)), V).
apply_binop(bor,  V1, V2, V) :- V is V1 \/ V2.
apply_binop(lt,   V1, V2, V) :- bool_value(V1 <  V2, V).
apply_binop(gt,   V1, V2, V) :- bool_value(V1 >  V2, V).
apply_binop(eq,   V1, V2, V) :- bool_value(V1 =:= V2, V).
apply_binop(ne,   V1, V2, V) :- bool_value(V1 =\= V2, V).
apply_binop(le,   V1, V2, V) :- bool_value(V1 =< V2, V).
apply_binop(ge,   V1, V2, V) :- bool_value(V1 >= V2, V).

%!  bool_value(:Test, -V) is det.
%   V = 1 if the (ground, decidable) test succeeds and V = 0 otherwise (Lean: ofBool).
bool_value(Test, V) :-
    (   call(Test)
    ->  V = 1
    ;   V = 0
    ).

%!  is_true(+V) is semidet.
%   is_true?(v): v is nonzero (Lean: IsTrue).
is_true(V) :- V =\= 0.

%!  is_false(+V) is semidet.
%   is_false?(v): v is zero (Lean: IsFalse).
is_false(V) :- V =:= 0.
