enum Severity {INFO, WARNING, CRITIQUE }

public class Checker {
    /*@ public normal_behaviour
      @ ensures \result != null;
      @*/
    Severity checkIt() {
        return Severity.INFO;
    }

    /*@ public normal_behaviour
      @  requires \static_invariant_for(Severity);
      @  ensures \result == 1;
      @*/
    int ord() {
        return Severity.WARNING.ordinal();
    }

    /*@ public normal_behaviour
      @  ensures \result != Severity.CRITIQUE;
      @*/
    Severity different() {
        return Severity.INFO;
    }
}