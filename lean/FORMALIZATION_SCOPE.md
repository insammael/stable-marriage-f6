# Formalization scope

This package intentionally does NOT claim an end-to-end Lean formalization of
the Stable Marriage theorem f(6)=48.

Kernel-checked layers bundled here:

1. `F6SmallBlockTokenCapacity.lean`
   Abstract fixed-partner-token run:
   - participation count;
   - <=2 men => <=1 step;
   - <=3 men => <=2 steps;
   - <=6 men => <=15 steps.

2. `F6RotationSupportCI2.lean`
   Abstract rotation-support/poset layer:
   from six-agent support bounds, minimum support 2, shared-support
   comparability, and the two small-block capacity hypotheses, derive
   - width <=3;
   - CI2.

   The capacity hypotheses remain explicit theorem arguments. They are not
   hidden assumptions.

3. `F6ConvexWindow.lean`, `F6ConvexWindowFull.lean`,
   `F6ConvexWindowN15.lean`
   Pure finite-poset layer:
   - Dilworth bridge;
   - pair/triple bounds;
   - n=15 endpoint refinement;
   - final theorem:
       WidthLE 3 + CI2 + card <=15
       => totalAntichains <=48.

Not formalized in this package:
- the classical Stable Marriage rotation definitions and exposure theorem;
- stable matchings <-> rotation-poset downsets;
- the human convex-window -> fixed-token-run semantic bridge;
- the manuscript's general order-N support-budget proposition;
- the lower-bound 48 construction.

Those items are proved/cited in the human manuscript. The Lean package is a
verification of the new finite combinatorial core, not a substitute for the
manuscript proof.
