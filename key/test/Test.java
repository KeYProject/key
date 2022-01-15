class Test {
    //@ public invariant MY_SUPER_INVARIANT: CONST == 42;

    public final int CONST = 42;
    /*@
    requires Z: this != null;
    ensures A: \result == 42;
    ensures B: \result >= 0;
    ensures C: \result != 0;
    */
    public int foo() {return CONST;}
}