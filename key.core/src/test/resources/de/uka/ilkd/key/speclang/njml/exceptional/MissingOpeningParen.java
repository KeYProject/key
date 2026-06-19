// msgContains mismatched input ')'
// position 7/32

class MissingOpeningParen {

    /*@ public normal_behaviour
      @   requires a.length > 0);
      @*/
    public int m(int a[]) { return 42; }
}
