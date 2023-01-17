class WhileAndSwitch {
    // java doesn't like while (false) and similar constructs
    boolean f = false;
    boolean t = true;
    /*@ invariant
      @ f == false &&
      @ t == true;
      @*/

    /*@ public normal_behavior
      @ requires a >= 0;
      @ ensures \result <==> a % 2 == 0;
      @ assignable \nothing;
      @*/
    public boolean m(int a) {
        // To prove this use loop treatment expand
        // or manually unwind the loops
        switch (a % 4) {
            case 0:
                while (t) break;
                return true;
            case 1:
                return false;
            case 2:
                while (t) return true;
                return false;
            case 3:
                while (f) return true;
                return false;
        }
        throw new Error("This should not happen");
    }
}
