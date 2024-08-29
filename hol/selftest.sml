open HolKernel boolLib Parse bossLib;
open pairTheory optionTheory stringTheory;

open ottLib;

val _ = ottDefine "test_def" 
 `(test T = T) /\ (test F = T)`;
