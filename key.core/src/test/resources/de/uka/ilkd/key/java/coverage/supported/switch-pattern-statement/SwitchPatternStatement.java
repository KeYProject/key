public class SwitchPatternStatement {
    int f(Object o) {
        int r;
        switch (o) {
            case String s: r = 1; break;
            default: r = 0;
        }
        return r;
    }
}
