
(* Algebraic hierarchies for Dummies

  Joint work with Cyril Cohen and Kazuhiko Sakaguchi
  https://hal.inria.fr/hal-02478907
  https://github.com/math-comp/hierarchy-builder

  STAMP seminars, 4/3/2020
*)
From hb Require Import hb.
From Coq Require Import ssreflect ssrfun.
From Coq Require ZArith.


HB.mixin Record CMonoid_of_Type A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  addrC : commutative add;
  add0r : left_id zero add;
}.

HB.structure CMonoid CMonoid_of_Type.axioms.

Print Module CMonoid_of_Type.
Print Module CMonoid.

Notation "0" := zero.
Infix "+" := add.

Check 0.
Check forall M : CMonoid.type, forall x : M, x + x = 0.
Check @addrC : forall M : CMonoid.type, forall x y : M, x + y = y + x.

HB.mixin Record AbelianGrp_of_CMonoid (A : Type) (_ : CMonoid.axioms A) := {
  opp : A -> A;
  addNr : left_inverse zero opp add; (* where does add come from? Why is it compatible with A? *)
}.

HB.structure AbelianGrp  CMonoid.axioms   AbelianGrp_of_CMonoid.axioms .

Notation "- x" := (opp x).

Check forall G : AbelianGrp.type, forall x : G, x + - x = 0.

HB.mixin Record SemiRing_of_CMonoid A of CMonoid.axioms A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
  mul0r : left_zero zero mul;
  mulr0 : right_zero zero mul;
}.

HB.structure SemiRing CMonoid.axioms SemiRing_of_CMonoid.axioms.

Notation "1" := one.
Infix "*" := mul.

Check forall S : SemiRing.type, forall x : S, x * x = 0 + 1. (* can I use - here? *)

(* HB.structure Ring := AbelianGrp.axioms + SemiRing.axioms. *)
HB.structure Ring CMonoid.axioms 
                     AbelianGrp.axioms 
                     SemiRing.axioms.

Check forall R : Ring.type, forall x : R, x * - (1 + x) = 0 + 1.

HB.status.

Print Canonical Projections.
Print Graph.

Module Instance1.

  Import ZArith String.

  Definition Z_CMonoid := CMonoid_of_Type.Axioms Z
    0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.
  HB.instance Z Z_CMonoid.

  Definition Z_AbelianGrp := AbelianGrp_of_CMonoid.Axioms Z
    Z.opp Z.add_opp_diag_l.
  HB.instance Z Z_AbelianGrp.

  Definition Z_SemiRing := SemiRing_of_CMonoid.Axioms Z
    1%Z Z.mul Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l Z.mul_0_l Z.mul_0_r.
  HB.instance Z Z_SemiRing.

  Set Printing All.
  Check forall x : Z, x * - (1 + x) = 0 + 1.

End Instance1.


HB.factory Record Ring_of_Type A := {
  zero : A;
  add : A -> A -> A;
  opp : A -> A;
  one : A;
  mul : A -> A -> A;
  addrA : associative add;
  (* addrC : commutative add; *)
  add0r : left_id zero add;
  addr0 : right_id zero add; (* Extra *)
  addNr : left_inverse zero opp add;
  addrN : right_inverse zero opp add; (* Extra *)
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
  mul0r : left_zero zero mul;
  mulr0 : right_zero zero mul;
}.

HB.builders Context A (f : Ring_of_Type.axioms A).

  (* explore the context *)

  Infix "+" := add_f.
  Notation "- x" := (opp_f x).

  Lemma addrC_f : commutative add_f.
  Proof.
  have addKl (a b c : A) : a + b = a + c -> b = c.
    apply: can_inj (add_f a) (add_f (- a)) _ _ _.
    by move=> x; rewrite addrA_f addNr_f add0r_f.
  have addKr (a b c : A) : b + a = c + a -> b = c.
    apply: can_inj (add_f ^~ a) (add_f ^~ (- a)) _ _ _.
    by move=> x; rewrite /= -addrA_f addrN_f addr0_f.
  have innerC (a b : A) : a + b + (a + b) = a + a + (b + b).
    by rewrite -[a+b]mul1r_f -mulrDl_f mulrDr_f !mulrDl_f !mul1r_f .
  move=> x y; apply: addKl (x) _ _ _; apply: addKr (y) _ _ _.
  by rewrite -!addrA_f [in RHS]addrA_f innerC !addrA_f.
  Qed.

  Definition to_CMonoid := CMonoid_of_Type.Axioms A
    zero_f add_f addrA_f addrC_f add0r_f.
  HB.instance A to_CMonoid.

  Definition to_AbelianGrp := AbelianGrp_of_CMonoid.Axioms A
    opp_f addNr_f.
  HB.instance A to_AbelianGrp.

  Definition to_SemiRing := SemiRing_of_CMonoid.Axioms A
    one_f mul_f mulrA_f mul1r_f mulr1_f mulrDl_f mulrDr_f mul0r_f mulr0_f.
  HB.instance A to_SemiRing.

HB.end.

HB.status.

Module Instance2.

  Import ZArith String.

  Definition Z_Ring := Ring_of_Type.Axioms Z
    0%Z Z.add Z.opp 1%Z Z.mul
    Z.add_assoc (*Z.add_comm*) Z.add_0_l Z.add_0_r
    Z.add_opp_diag_l Z.add_opp_diag_r Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l Z.mul_0_l Z.mul_0_r.
  HB.instance Z Z_Ring.

  Set Printing All.
  Check forall x : Z, x * - x = 0 + 1.

End Instance2.

(* show Puzzle*)
(* show hb.elpi: declare-structure *)