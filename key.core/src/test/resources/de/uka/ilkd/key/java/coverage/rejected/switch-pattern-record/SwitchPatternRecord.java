public class SwitchPatternRecord {
    record Point(int x, int y) { }
    int f(Object o) {
        int r;
        switch (o) {
            case Point(int x, int y): r = x + y; break;
            default: r = 0;
        }
        return r;
    }
}
