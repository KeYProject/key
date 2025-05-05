class C {
    int f;
    final int finf;
    C next;
}

class Csub extends C {
    int f; // hiding the field f in C.
    final int finf;
}
