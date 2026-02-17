open HolKernel boolLib Parse bossLib ottLib;

val _ = ottDefine "test_def" `
   (test T = T)
/\ (test F = T)
`;
