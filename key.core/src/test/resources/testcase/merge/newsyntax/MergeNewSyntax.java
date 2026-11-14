public class MergeNewSyntax {

    int y;

    /*@ public normal_behavior
      @   ensures \result >= 0;
      @*/
    int bare(int a) {
        int r;
        if (a > 0) {
            r = a;
        } else {
            r = -a;
        }
        //@ merge_point;
        return r;
    }

    /*@ public normal_behavior
      @   ensures \result >= 0;
      @*/
    int byId(int a) {
        int r;
        if (a > 0) {
            r = a;
        } else {
            r = -a;
        }
        //@ merge_point \by MergeByFullAnonymization;
        return r;
    }

    /*@ public normal_behavior
      @   ensures \result >= 0;
      @*/
    int param(int a) {
        int r;
        if (a > 0) {
            r = a;
        } else {
            r = -a;
        }
        //@ merge_point \by "MergeByPredicateAbstraction" \lattice conjunctive \predicate (int x) : x >= 0, x == \old(y);
        return r;
    }
}
