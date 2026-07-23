public class SwitchExpr {
    int f(int x) {
        return switch (x) {
            case 1 -> 10;
            case 2 -> { yield 20; }
            default -> 0;
        };
    }
}
