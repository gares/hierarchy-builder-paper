From mathcomp Require Import all.

Check (Choice.type : Type).
Check (CountRing.ClosedField.type : Type).
Check (CountRing.ComRing.type : Type).
Check (CountRing.ComUnitRing.type : Type).
Check (CountRing.DecidableField.type : Type).
Check (CountRing.Field.type : Type).
Check (CountRing.IntegralDomain.type : Type).
Check (CountRing.Ring.type : Type).
Check (CountRing.UnitRing.type : Type).
Check (CountRing.Zmodule.type : Type).
Check (Countable.type : Type).
Check (Equality.type : Type).
Fail Check (Falgebra.type : Type).
Fail Check (FieldExt.type : Type).
Check (FinGroup.type : Type).
Fail Check (FinRing.Algebra.type : Type).
Check (FinRing.ComRing.type : Type).
Check (FinRing.ComUnitRing.type : Type).
Check (FinRing.Field.type : Type).
Check (FinRing.IntegralDomain.type : Type).
Fail Check (FinRing.Lalgebra.type : Type).
Fail Check (FinRing.Lmodule.type : Type).
Check (FinRing.Ring.type : Type).
Fail Check (FinRing.UnitAlgebra.type : Type).
Check (FinRing.UnitRing.type : Type).
Check (FinRing.Zmodule.type : Type).
Check (Finite.type : Type).
Fail Check (GRing.Algebra.type : Type).
Check (GRing.ClosedField.type : Type).
Fail Check (GRing.ComAlgebra.type : Type).
Check (GRing.ComRing.type : Type).
Fail Check (GRing.ComUnitAlgebra.type : Type).
Check (GRing.ComUnitRing.type : Type).
Check (GRing.DecidableField.type : Type).
Check (GRing.Field.type : Type).
Check (GRing.IntegralDomain.type : Type).
Fail Check (GRing.Lalgebra.type : Type).
Fail Check (GRing.Lmodule.type : Type).
Check (GRing.Ring.type : Type).
Fail Check (GRing.UnitAlgebra.type : Type).
Check (GRing.UnitRing.type : Type).
Check (GRing.Zmodule.type : Type).
Check (Num.ArchimedeanField.type : Type).
Check (Num.ClosedField.type : Type).
Fail Check (Num.NormedZmodule.type : Type).
Check (Num.NumDomain.type : Type).
Check (Num.NumField.type : Type).
Check (Num.RealClosedField.type : Type).
Check (Num.RealDomain.type : Type).
Check (Num.RealField.type : Type).
Fail Check (Order.BDistrLattice.type : Type).
Fail Check (Order.BLattice.type : Type).
Fail Check (Order.CBDistrLattice.type : Type).
Fail Check (Order.CTBDistrLattice.type : Type).
Fail Check (Order.DistrLattice.type : Type).
Fail Check (Order.FinCDistrLattice.type : Type).
Fail Check (Order.FinDistrLattice.type : Type).
Fail Check (Order.FinLattice.type : Type).
Fail Check (Order.FinPOrder.type : Type).
Fail Check (Order.FinTotal.type : Type).
Fail Check (Order.Lattice.type : Type).
Fail Check (Order.POrder.type : Type).
Fail Check (Order.TBDistrLattice.type : Type).
Fail Check (Order.TBLattice.type : Type).
Fail Check (Order.Total.type : Type).
Fail Check (SplittingField.type : Type).
Fail Check (Vector.type : Type).
(*
37 structures have no parameter and other 30 structures have parameters:
$ grep -c '^Check' count_noparam.v
37
$ grep -c '^Fail Check' count_noparam.v
30
*)
