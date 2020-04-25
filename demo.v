From Coq Require Import ssreflect ssrfun ZArith.
From HB Require Import structures.

Module V1.

HB.mixin Record Monoid_of_Type A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure Definition Monoid := { A of Monoid_of_Type A }.

HB.mixin Record Ring_of_Monoid A of Monoid A := {
  one : A;
  opp : A -> A;
  mul : A -> A -> A;
  addNr : left_inverse zero opp add;
  addrN : right_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.
HB.structure Definition Ring := { A of Monoid A & Ring_of_Monoid A }.

Declare Scope hb_scope.
Delimit Scope hb_scope with G.
Open Scope hb_scope.
Notation "0" := zero : hb_scope.
Notation "1" := one : hb_scope.
Infix "+" := (@add _) : hb_scope.
Notation "- x" := (@opp _ x) : hb_scope.
Infix "*" := (@mul _) : hb_scope.
Notation "x - y" := (x + - y) : hb_scope.

(* Theory *)

(* https://math.stackexchange.com/questions/346375/commutative-property-of-ring-addition/346682 *)
Lemma addrC { R : Ring.type} : commutative (@add R).
Proof.
have addKl (a b c : R) : a + b = a + c -> b = c.
  apply: can_inj (add a) (add (-a)) _ _ _.
  by move=> x; rewrite addrA addNr add0r.
have addKr (a b c : R) : b + a = c + a -> b = c.
  apply: can_inj (add ^~ a) (add ^~ (-a)) _ _ _.
  by move=> x; rewrite /= -addrA addrN addr0.
have innerC (a b : R) : a + b + (a + b) = a + a + (b + b).
  by rewrite -[a+b]mul1r -mulrDl mulrDr !mulrDl !mul1r.
move=> x y; apply: addKl (x) _ _ _; apply: addKr (y) _ _ _.
by rewrite -!addrA [in RHS]addrA innerC !addrA.
Qed.

End V1.

Module V2.

HB.mixin Record Monoid_of_Type A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure Definition Monoid := { A of Monoid_of_Type A }.

HB.mixin Record AbelianGroup_of_Monoid A of Monoid A := {
  opp : A -> A;
  addrC : commutative (add : A -> A -> A);
  addNr : left_inverse zero opp add;
}.
HB.structure Definition AbelianGroup :=
  { A of Monoid A & AbelianGroup_of_Monoid A }.

HB.mixin Record Ring_of_AbelianGroup A of AbelianGroup A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;              mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;   mulrDr : right_distributive mul add;
}.
HB.structure Definition Ring := { A of AbelianGroup A & Ring_of_AbelianGroup A }.
Lemma addrN {R : AbelianGroup.type} : right_inverse (@zero R) opp add.
Proof. by move=> x; rewrite addrC addNr. Qed.

Declare Scope hb_scope.
Delimit Scope hb_scope with G.
Open Scope hb_scope.
Notation "0" := zero : hb_scope.
Notation "1" := one : hb_scope.
Infix "+" := (@add _) : hb_scope.
Notation "- x" := (@opp _ x) : hb_scope.
Infix "*" := (@mul _) : hb_scope.
Notation "x - y" := (x + - y) : hb_scope.

Check addrC. (* It is not a lemma anymore *)

End V2.

Module V3.

HB.mixin Record Monoid_of_Type A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure Definition Monoid := { A of Monoid_of_Type A }.

HB.mixin Record AbelianGroup_of_Monoid A of Monoid A := {
  opp : A -> A;
  addrC : commutative (add : A -> A -> A);
  addNr : left_inverse zero opp add;
}.
HB.structure Definition AbelianGroup := { A of Monoid A & AbelianGroup_of_Monoid A }.

HB.mixin Record Ring_of_AbelianGroup A of AbelianGroup A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.
HB.structure Definition Ring := { A of AbelianGroup A & Ring_of_AbelianGroup A }.

Declare Scope hb_scope.
Delimit Scope hb_scope with G.
Open Scope hb_scope.
Notation "0" := zero : hb_scope.
Notation "1" := one : hb_scope.
Infix "+" := (@add _) : hb_scope.
Notation "- x" := (@opp _ x) : hb_scope.
Infix "*" := (@mul _) : hb_scope.
Notation "x - y" := (x + - y) : hb_scope.

Lemma addrN {R : AbelianGroup.type} : right_inverse (zero : R) opp add.
Proof. by move=>x; rewrite addrC addNr. Qed.

HB.factory Record Ring_of_Monoid A of Monoid A := {
  one : A;
  opp : A -> A;
  mul : A -> A -> A;
  addNr : left_inverse zero opp add;
  addrN : right_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.

HB.builders Context A (f : Ring_of_Monoid A).

  Lemma addrC : commutative (add : A -> A -> A).
  Proof.
  have addKl (a b c : A) : a + b = a + c -> b = c.
    apply: can_inj (add a) (add (opp_f a)) _ _ _.
    by move=> x; rewrite addrA addNr_f add0r.
  have addKr (a b c : A) : b + a = c + a -> b = c.
    apply: can_inj (add ^~ a) (add ^~ (opp_f a)) _ _ _.
    by move=> x; rewrite /= -addrA addrN_f addr0.
  have innerC (a b : A) : a + b + (a + b) = a + a + (b + b).
    by rewrite -[a+b]mul1r_f -mulrDl_f mulrDr_f !mulrDl_f !mul1r_f .
  move=> x y; apply: addKl (x) _ _ _; apply: addKr (y) _ _ _.
  by rewrite -!addrA [in RHS]addrA innerC !addrA.
  Qed.

  Definition to_AbelianGroup_of_Monoid :=
    AbelianGroup_of_Monoid.Build A opp_f addrC addNr_f.
  HB.instance A to_AbelianGroup_of_Monoid.

  Definition to_Ring_of_AbelianGroup :=
    Ring_of_AbelianGroup.Build A one_f mul_f
      mulrA_f mul1r_f mulr1_f mulrDl_f mulrDr_f.
  HB.instance A to_Ring_of_AbelianGroup.

HB.end.

End V3.

Module V4.

HB.mixin Record Monoid_of_Type A := {
  zero : A;
  add : A -> A -> A;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure Definition Monoid := { A of Monoid_of_Type A }.

HB.mixin Record AbelianGroup_of_Monoid A of Monoid A := {
  opp : A -> A;
  addrC : commutative (add : A -> A -> A);
  addNr : left_inverse zero opp add;
}.
HB.structure Definition AbelianGroup := { A of Monoid A & AbelianGroup_of_Monoid A }.

HB.mixin Record SemiRing_of_Monoid A of Monoid A := {
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
HB.structure Definition SemiRing := { A of Monoid A & SemiRing_of_Monoid A }.

Declare Scope hb_scope.
Delimit Scope hb_scope with G.
Open Scope hb_scope.
Notation "0" := zero : hb_scope.
Notation "1" := one : hb_scope.
Infix "+" := (@add _) : hb_scope.
Notation "- x" := (@opp _ x) : hb_scope.
Infix "*" := (@mul _) : hb_scope.
Notation "x - y" := (x + - y) : hb_scope.

Lemma addrN {R : AbelianGroup.type} : right_inverse (zero : R) opp add.
Proof. by move=>x; rewrite addrC addNr. Qed.

HB.factory Record Ring_of_AbelianGroup A of AbelianGroup A := {
  one : A;
  mul : A -> A -> A;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.

HB.builders Context (A : Type) (f : Ring_of_AbelianGroup A).

  Fact mul0r : left_zero zero mul_f.
  Proof.
  move=> x; rewrite -[LHS]add0r addrC.
  rewrite -{2}(addNr (mul_f x x)) (addrC (opp _)) addrA.
  by rewrite -mulrDl_f add0r addrC addNr.
  Qed.

  Fact mulr0 : right_zero zero mul_f.
  Proof.
  move=> x; rewrite -[LHS]add0r addrC.
  rewrite -{2}(addNr (mul_f x x)) (addrC (opp _)) addrA.
  by rewrite -mulrDr_f add0r addrC addNr.
  Qed.

  Definition to_SemiRing_of_Monoid := SemiRing_of_Monoid.Build A
    _ mul_f mulrA_f mul1r_f mulr1_f
    mulrDl_f mulrDr_f mul0r mulr0.
  HB.instance A to_SemiRing_of_Monoid.

HB.end.
HB.structure Definition Ring := { A of AbelianGroup A & Ring_of_AbelianGroup A }.

HB.factory Record Ring_of_Monoid A of Monoid A := {
  one : A;
  opp : A -> A;
  mul : A -> A -> A;
  addNr : left_inverse zero opp add;
  addrN : right_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.

HB.builders Context (A : Type) (f : Ring_of_Monoid A).

  Lemma addrC : commutative (add : A -> A -> A).
  Proof.
  have innerC (a b : A) : a + b + (a + b) = a + a + (b + b).
    by rewrite -[a+b]mul1r_f -mulrDl_f mulrDr_f !mulrDl_f !mul1r_f.
  have addKl (a b c : A) : a + b = a + c -> b = c.
    apply: can_inj (add a) (add (opp_f a)) _ _ _.
    by move=> x; rewrite addrA addNr_f add0r.
  have addKr (a b c : A) : b + a = c + a -> b = c.
    apply: can_inj (add ^~ a) (add ^~ (opp_f a)) _ _ _.
    by move=> x; rewrite /= -addrA addrN_f addr0.
  move=> x y; apply: addKl (x) _ _ _; apply: addKr (y) _ _ _.
  by rewrite -!addrA [in RHS]addrA innerC !addrA.
  Qed.

  Definition to_AbelianGroup_of_Monoid :=
    AbelianGroup_of_Monoid.Build A opp_f addrC addNr_f.
  HB.instance A to_AbelianGroup_of_Monoid.

  Definition to_Ring_of_AbelianGroup :=
    Ring_of_AbelianGroup.Build A one_f mul_f
      mulrA_f mul1r_f mulr1_f mulrDl_f mulrDr_f.
  HB.instance A to_Ring_of_AbelianGroup.

HB.end.

End V4.

Import V4. (* V1, V3 and V4, they all work! V2 does not. *)

Definition Z_monoid_axioms : Monoid_of_Type Z :=
  Monoid_of_Type.Build Z 0%Z Z.add Z.add_assoc Z.add_0_l Z.add_0_r.

HB.instance Z Z_monoid_axioms.

Definition Z_ring_axioms : Ring_of_Monoid Z :=
  Ring_of_Monoid.Build Z 1%Z Z.opp Z.mul
    Z.add_opp_diag_l Z.add_opp_diag_r
    Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.

HB.instance Z Z_ring_axioms.

Lemma exercise (m n : Z) : (n + m) - n * 1 = m.
Proof. by rewrite mulr1 (addrC n) -(addrA m) addrN addr0. Qed.
