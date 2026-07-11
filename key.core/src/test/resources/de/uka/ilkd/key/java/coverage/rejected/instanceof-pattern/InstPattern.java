public class InstPattern {
    int f(Object o) {
        if (o instanceof String s) { return s.length(); }
        return 0;
    }
}
