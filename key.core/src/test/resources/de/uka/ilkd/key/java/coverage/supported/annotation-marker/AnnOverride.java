public class AnnOverride {
    static class A { int f() { return 1; } }
    static class B extends A { @Override int f() { return 2; } }
}
