// noException: true
// verbose: true

// Positive control for the class level "field-like" clause handling: captures/duration/
// working_space are accepted drops. They must be silently removed, must not become spurious
// fields, and must not raise an exception.

class DeprecatedDrops {

    //@ captures captured;
    //@ duration \duration_TICKS;
    //@ working_space ws;

    //@ ghost int g = 0;

    /*@ public normal_behavior
      @   ensures \result == g;
      @*/
    public int m() { return g; }
}
