public class GenMethod {
    <T> T id(T x) { return x; }
    String f() { return id("hi"); }
}
