public class RecordPattern {
    record Point(int x, int y) { }
    int f(Object o) {
        if (o instanceof Point(int a, int b)) { return a + b; }
        return 0;
    }
}
