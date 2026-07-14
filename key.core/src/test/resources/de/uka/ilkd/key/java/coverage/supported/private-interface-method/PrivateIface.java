public class PrivateIface {
    interface I {
        int pub();
        private int helper() { return 5; }
        default int use() { return helper() + pub(); }
    }
    static class C implements I { public int pub() { return 1; } }
    int f() { return new C().use(); }
}
