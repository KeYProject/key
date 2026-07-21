public class NestedStatic {
    static class Inner { int v; }
    int f() { Inner i = new Inner(); i.v = 2; return i.v; }
}
