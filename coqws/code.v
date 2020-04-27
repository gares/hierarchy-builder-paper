Require Import ZArith.
From HB Require Import structures.
From Coq Require Import ssreflect ssrfun ssrbool.

HB.mixin Record CMonoid_of_Type A := { (* The set of axioms making A a commutative monoid. *)
  zero  : A;
  add   : A -> A -> A;
  addrA : associative add;  (* `add` is associative  *)
  addrC : commutative add;  (* `add` is commutative  *)
  add0r : left_id zero add; (* `zero` is the neutral *)
}.
HB.structure Definition CMonoid := { A of CMonoid_of_Type A }. (* The structure thereof. *)
Notation "0" := zero.
Infix    "+" := add.

(* The type of the operations and axioms depend on a CMonoid.type structure. *)
Check addrC. (* ?M : CMonoid.type |- forall x y : ?M, x + y = y + x *)

HB.mixin Record AbelianGrp_of_CMonoid A of CMonoid A := {
  (* We can write `add` here since A is a  CMonoid   *)
  opp   : A -> A;
  addNr : left_inverse zero opp add; (* `opp` is the additive inverse *)
}.


HB.structure Definition AbelianGrp := { A of AbelianGrp_of_CMonoid A & }.
Notation "- x"   := (opp x).
Notation "x - y" := (add x (opp y)).

(* A statement in the signature of an Abelian group G. *)
Check forall G : AbelianGrp.type, forall x : G, x - x = 0.

HB.mixin Record SemiRing_of_CMonoid A of CMonoid A := {
  one    : A;
  mul    : A -> A -> A;
  mulrA  : associative mul;  (* `mul` is associative   *)
  mul1r  : left_id one mul;  (* `one` is left neutral  *)
  mulr1  : right_id one mul; (* `one` is right neutral *)
  mulrDl : left_distributive mul add;  (* `mul` distributes over *)
  mulrDr : right_distributive mul add; (*   `add` on both sides  *)
  mul0r  : left_zero zero mul;  (* `zero` is absorbing `mul`     *)
  mulr0  : right_zero zero mul; (*   on both sides               *)
}.
HB.structure Definition SemiRing := { A of SemiRing_of_CMonoid A & }.
Notation "1"  := one.
Notation "-1" := (- one).
Infix    "*"  := mul.

(* A statement in the signature of a `SemiRing` S.  *)
Check forall S : SemiRing.type, forall x : S, x * 1 + 0 = x.

(* We need no additional mixin to declare the `Ring` structure. *)
HB.structure Definition Ring := { A of SemiRing_of_CMonoid A & AbelianGrp_of_CMonoid A }.

(* A statement in the signature of a Ring R.  *)
Check forall R : Ring.type, forall x : R, x * -1 = - x.

(* We equip Z with the structures of CMonoid, AbelianGrp and SemiRing; HB equips it with Ring. *)
Definition Z_CMonoid    := CMonoid_of_Type.Build Z 0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.
HB.instance Z Z_CMonoid.
Definition Z_AbelianGrp := AbelianGrp_of_CMonoid.Build Z Z.opp Z.add_opp_diag_l.
HB.instance Z Z_AbelianGrp.
Definition Z_SemiRing   := SemiRing_of_CMonoid.Build Z 1%Z Z.mul Z.mul_assoc Z.mul_1_l
  Z.mul_1_r Z.mul_add_distr_r Z.mul_add_distr_l (fun _ => erefl) Zmult_0_r.
HB.instance Z Z_SemiRing.

(* A statement in the signature of the Z ring *)
Check forall x : Z, x * - (1 + x) = 0 + 1.
