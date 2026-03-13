// NOTE: This is currently not giving a good error message
// broken: true
// msgContains: this.*.* is not a valid location set expression
// position: 9/28

class ThisStarStar {

    int max;

    /*@ public normal_behaviour
      @   assignable this.*.*;
      @*/
    public int m(int a[]) { return 0; }

}


/*
TermCreationException: Building a term failed. Normally there is an arity mismatch or one of the subterms' sorts is not compatible (e.g. like the '2' in "true & 2")
The top level operator was allFields(Sort: LocSet); its expected arg sorts were:
1.) sort: java.lang.Object, sort hash: 1108066952

The subterms were:
1.) allFields(self)(sort: LocSet, sort hash: 1253633245)
*/
