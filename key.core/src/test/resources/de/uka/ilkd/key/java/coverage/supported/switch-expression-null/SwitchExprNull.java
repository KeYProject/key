public class SwitchExprNull {
    int f(String s) {
        return switch (s) {
            case null -> -1;
            default -> 0;
        };
    }
}
