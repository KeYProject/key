public class RecordPattern {
    record Point(int x, int y) { }
    record Box(Object value) { }

    int f(Object o) {
        if (o instanceof Point(int a, int b)) { return a + b; }
        return 0;
    }

    Object g(Object o) {
        if (o instanceof Box(Object value)) { return value; }
        return null;
    }

    Object h(Object o) {
        if (o instanceof Box(var value)) { return value; }
        return null;
    }
}
