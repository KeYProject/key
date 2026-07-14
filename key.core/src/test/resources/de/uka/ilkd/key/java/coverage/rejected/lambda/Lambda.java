public class Lambda {
    Runnable r = () -> { };
    int f() { r.run(); return 1; }
}
