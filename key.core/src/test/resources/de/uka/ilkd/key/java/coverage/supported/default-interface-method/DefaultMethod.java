public class DefaultMethod {
    interface Greeter {
        int base();
        default int greet() { return base() + 1; }
    }
    static class G implements Greeter { public int base() { return 10; } }
    int f() { return new G().greet(); }
}
