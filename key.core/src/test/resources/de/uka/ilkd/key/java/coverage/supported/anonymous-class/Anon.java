public class Anon {
    interface Sup { int val(); }
    int f() {
        Sup s = new Sup() { public int val() { return 42; } };
        return s.val();
    }
}
