// noException: true
// verbose: true

// Positive control for the `\sum` quantifier round-trip: JMLtk parses the ensures clause and
// JmlToTextual must re-emit `\sum` verbatim so KeY's own grammar can re-parse it (no silent
// spec weakening).

class SumClause {

    /*@ public normal_behavior
      @   ensures \result == (\sum int i; 0 <= i && i < a.length; a[i]);
      @*/
    int sumAll(int[] a) {
        int s = 0;
        for (int i = 0; i < a.length; i++) {
            s += a[i];
        }
        return s;
    }

    /*@ public normal_behavior
      @   ensures (\sum int j; 0 <= j && j < a.length; (\bigint)a[j]) >= 0;
      @*/
    int sumBig(int[] a) {
        return 0;
    }
}
