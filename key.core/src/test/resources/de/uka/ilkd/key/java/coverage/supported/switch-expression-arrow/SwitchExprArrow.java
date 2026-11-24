public class SwitchExprArrow {
    int f(int x) {
        return switch (x) {
            case 1 -> 10;
            default -> 0;
        };
    }
}
