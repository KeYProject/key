public class GenWildcard {
    static class Box<T> { T v; }
    int size(Box<?> b) { return 0; }
    int f(Box<? extends Object> b) { return 1; }
}
