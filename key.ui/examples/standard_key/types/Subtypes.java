class A {

    int f;

    //@ ghost \TYPE packed;
    //@ invariant packed <: \type(A) ==> f > 0;
}

class B extends A {
    //@ invariant packed <: \type(B) ==> f > 1;

    //@ requires this.packed == \type(B);
    //@ ensures f > 0;
    //@ ensures f > 1;
    void subtypes() {}
}
