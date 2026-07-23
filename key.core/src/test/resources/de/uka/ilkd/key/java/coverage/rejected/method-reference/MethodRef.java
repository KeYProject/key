public class MethodRef {
    interface Fn { int apply(String s); }
    int len(String s) { return s.length(); }
    Fn f = this::len;
}
