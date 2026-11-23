/- Copyright 2009-2026 EPFL, Lausanne -/

import Stainless.Semantics

/-!
# `InoxEncoder` on integer division

Stainless's `BigInt` division and remainder are the JVM's, which round toward zero. Inox's are
euclidean, so `InoxEncoder` (`core/src/main/scala/stainless/solvers/InoxEncoder.scala`) encodes
`lhs / rhs` as

```scala
val a = lhs
val q = (if (a >= 0) a else -a) / rhs
if (a >= 0) q else -q
```

and `lhs % rhs` the same way with `%`. This file proves that the encoding gives the result of
Stainless's division, including on a zero divisor, where both get stuck. `lhs` evaluates to an
integer, as Stainless's typing ensures, and binding `a` doesn't change the value of `rhs`, which the encoder ensures by
choosing a fresh `a`.
-/

namespace Stainless.Semantics.Encoder

open Stainless.Semantics

/-- The encoding of `lhs / rhs` (with `Division`) or `lhs % rhs` (with `Remainder`), with the
fresh variables `a` and `q`. -/
def encodeJVM (op : Expr → Expr → Expr) (lhs rhs : Expr) (a q : Id) : Expr :=
  let nonNegative := Expr.GreaterEquals (Expr.Variable a) (Expr.IntegerLiteral 0)
  Expr.Let a lhs
    (Expr.Let q (op (Expr.IfExpr nonNegative (Expr.Variable a) (Expr.UMinus (Expr.Variable a))) rhs)
      (Expr.IfExpr nonNegative (Expr.Variable q) (Expr.UMinus (Expr.Variable q))))

theorem division (O : Oracle) (P : Program) (fuel : Int) (env : Env) (lhs rhs : Expr) (a q : Id)
    (hq : q ≠ a)
    (hlhs : ∀ v, eval O P fuel env lhs = .Ok v → ∃ x, v = .IntV x)
    (hrhs : ∀ v, eval O P fuel (env_bind env a v) rhs = eval O P fuel env rhs) :
    eval O P fuel env (encodeJVM .Division lhs rhs a q) = eval O P fuel env (.JVMDivision lhs rhs) := by
  obtain ⟨tys, vars⟩ := env
  unfold encodeJVM
  simp only [eval]
  cases hl : eval O P fuel (Env.Env tys vars) lhs with
  | Ok v =>
    obtain ⟨x, rfl⟩ := hlhs _ hl
    simp only [hrhs]
    cases hr : eval O P fuel (Env.Env tys vars) rhs with
    | Ok b =>
      cases b with
      | IntV y =>
        by_cases hy : y = 0
        · by_cases hx : (0 : Int) ≤ x <;>
            simp [eval_bool, eval, zero_divisor, env_vars, env_bind, lookup_var, arith_le, arith_lt, arith_neg, arith_div,
              hx, hy]
        · by_cases hx : (0 : Int) ≤ x <;>
            simp [eval_bool, eval, zero_divisor, env_vars, env_bind, lookup_var, arith_le, arith_lt, arith_neg, arith_div,
              tdiv, hx, hy, Ne.symm hq]
      | BVV s w y =>
        by_cases hy : y = 0 <;> by_cases hx : (0 : Int) ≤ x <;>
          simp [eval_bool, eval, zero_divisor, env_vars, env_bind, lookup_var, arith_le, arith_lt, arith_neg, arith_div,
            hx, hy]
      | _ =>
        by_cases hx : (0 : Int) ≤ x <;>
          simp [eval_bool, eval, zero_divisor, env_vars, env_bind, lookup_var, arith_le, arith_lt, arith_neg, arith_div,
            hx]
    | _ =>
      by_cases hx : (0 : Int) ≤ x <;>
        simp [eval_bool, eval, env_vars, env_bind, lookup_var, arith_le, arith_lt, arith_neg, hx]
  | _ => rfl

theorem remainder (O : Oracle) (P : Program) (fuel : Int) (env : Env) (lhs rhs : Expr) (a q : Id)
    (hq : q ≠ a)
    (hlhs : ∀ v, eval O P fuel env lhs = .Ok v → ∃ x, v = .IntV x)
    (hrhs : ∀ v, eval O P fuel (env_bind env a v) rhs = eval O P fuel env rhs) :
    eval O P fuel env (encodeJVM .Remainder lhs rhs a q) = eval O P fuel env (.JVMRemainder lhs rhs) := by
  obtain ⟨tys, vars⟩ := env
  unfold encodeJVM
  simp only [eval]
  cases hl : eval O P fuel (Env.Env tys vars) lhs with
  | Ok v =>
    obtain ⟨x, rfl⟩ := hlhs _ hl
    simp only [hrhs]
    cases hr : eval O P fuel (Env.Env tys vars) rhs with
    | Ok b =>
      cases b with
      | IntV y =>
        by_cases hy : y = 0
        · by_cases hx : (0 : Int) ≤ x <;>
            simp [eval_bool, eval, zero_divisor, env_vars, env_bind, lookup_var, arith_le, arith_lt, arith_neg, arith_rem,
              hx, hy]
        · by_cases hx : (0 : Int) ≤ x <;>
            simp [eval_bool, eval, zero_divisor, env_vars, env_bind, lookup_var, arith_le, arith_lt, arith_neg, arith_rem,
              trem, tdiv, hx, hy, Ne.symm hq, Int.emod_def]
          rw [Int.mul_neg]
          generalize y * (-x / y) = k
          omega
      | BVV s w y =>
        by_cases hy : y = 0 <;> by_cases hx : (0 : Int) ≤ x <;>
          simp [eval_bool, eval, zero_divisor, env_vars, env_bind, lookup_var, arith_le, arith_lt, arith_neg, arith_rem,
            hx, hy]
      | _ =>
        by_cases hx : (0 : Int) ≤ x <;>
          simp [eval_bool, eval, zero_divisor, env_vars, env_bind, lookup_var, arith_le, arith_lt, arith_neg, arith_rem,
            hx]
    | _ =>
      by_cases hx : (0 : Int) ≤ x <;>
        simp [eval_bool, eval, env_vars, env_bind, lookup_var, arith_le, arith_lt, arith_neg, hx]
  | _ => rfl

end Stainless.Semantics.Encoder
