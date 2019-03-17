public class Test {
  /*@ public normal_behavior
    @ requires i >= 0;
    @ ensures (\result == 0 || \result <= -1) && ((flag && \old(i) < 17) ==> \result == -2) ;
    @*/
  public static int loopScopeRuleBenchmark(int i, boolean flag) {
    k: {
      l:
      /*@ loop_invariant
        @   i >= 0 && i <= \old(i);
        @ decreases i;
        @*/
      while (i > 0) {
        if (i == 17) {
          i = 0;
          continue l; // have to prove the invariant
        } else if (i == 42) {
          i = -1;
          break l;    // have to prove the postcondition!
        } else if (i == 2048) {
          i = -1;
          break k;    // have to prove the postcondition
        }

        i--;
      }

      if (flag) {
        i = -2;
        break k;
      }
    }

    return i;
  }
}
