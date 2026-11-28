public class SwitchPatternGuard {
    int f(Object o) {
        int r;
        switch (o) {
            case Integer i when i.intValue() > 0: r = 1; break;
            default: r = 0;
        }
        return r;
    }
}
