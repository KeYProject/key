// noException: true
// verbose: true

// Positive control for the `\bsum` quantifier round-trip: JMLtk parses the ensures clause and
// JmlToTextual must re-emit `\bsum` verbatim so KeY's own grammar can re-parse it. `\bsum` uses
// the bounded range form `(\bsum <type> <var>; from; to; summand)`; it is a KeY extension that
// is accepted (and flagged deprecated with a warning) by the JML term translation.
//
// NB: `\bsum` must NOT use the `\sum`-style single-expression form
// `(\bsum int i; 0 <= i && i < a.length; a[i])` — that does not match KeY's `bsumterm`
// production and fails loudly at re-parse time, which is the correct (guarded) behavior.

class BsumClause {

    /*@ public normal_behavior
      @   ensures \result == (\bsum int i; 0; a.length; a[i]);
      @*/
    int bsumAll(int[] a) {
        int s = 0;
        for (int i = 0; i < a.length; i++) {
            s += a[i];
        }
        return s;
    }
}
