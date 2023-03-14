# Notes on a soundness bug

Some variables are implied zero at the beginning from the constraints:
- R87
- R85
- R83
- R81
- R11
- R69
- R67

Some variables are implied zero from experiments:
- R63
- (R65)
- R55
- R9
- R57

Will an instance with these propagated reproduce the bug? Yes.

## Step 1: spot the falsehood


This is true: severing transition 1 would indeed disconnect 3:
```
Sub-proof #1 shows that the following formulas are inconsistent:
----------------------------------------------------------------
  (1)  TransitionMask_1241529534(all_10_0, 6, 1, 0)
  (2)  Connected_1241529534(all_10_0, 6)
  (3)  TransitionMask_1241529534(all_10_0, 6, 3, 1)
```

This must come from:
```
|   (32)  TransitionMask_1241529534(all_10_0, 6, 1, all_10_26 + all_10_27)
|   (34)  TransitionMask_1241529534(all_10_0, 6, 3, -1*all_10_26 + -1*all_10_27 + R66 - R65)
```

How did (I) `all_10_26 + all_10_27 = 0` and (II) `-1*all_10_26 + -1*all_10_27 + R66 - R65) = 1`?

It seems the zeroing comes from (31) and (49) which leads to a cut on transition 0.

Note that setting R65 = 0 preserves satisfiability, and the bug. The logs become more complicated.

Hence, the bug comes from the incorrect conclusion (3), via (34). Why is (II) deduced?

This looks fishy:

```
THEORY_AXIOM uuverifiers.parikh_theory.RegisterCounting@4a003cbe: 
  (125)  \forall int v0, v1, v2, v3, v4;
         (TransitionMask_1241529534(v4, 7, 2, v2) ->
           !TransitionMask_1241529534(v4, 7, 1, v3) |
           !TransitionMask_1241529534(v4, 7, 0, -1*v3 +
             -1*v2 + 1) | !TransitionMask_1241529534(v4, 6,
             4, v1) | !TransitionMask_1241529534(v4, 6, 3,
             0) | !TransitionMask_1241529534(v4, 6, 2, v0)
           | !TransitionMask_1241529534(v4, 6, 1, 1) |
           !TransitionMask_1241529534(v4, 6, 0, 0) |
           !MonoidMap_1241529534(v4, 1, 0, 1, 1, 0, 1, 0,
             1, 0, 1, 1, 0))
```
