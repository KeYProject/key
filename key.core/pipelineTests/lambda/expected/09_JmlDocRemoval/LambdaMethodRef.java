import java.util.Objects;
import java.util.function.Function;
import java.util.function.Predicate;

class LambdaMethodRef {

    static class Box {

        Box(int size) {
        }
    }

    Predicate<Object> nullTest() {
        Predicate<Object> p = new Predicate__1();
        return p;
    }

    Function<String, Integer> length() {
        Function<String, Integer> f = new Function__1();
        return f;
    }

    Predicate<String> bounded() {
        String s = "abc";
        Predicate<String> p = new Predicate__2(s);
        return p;
    }

    Function<Integer, Box> factory() {
        Function<Integer, Box> f = new Function__2();
        return f;
    }

    private static final class Predicate__1 implements java.util.function.Predicate<java.lang.Object> {

        public boolean test(java.lang.Object p0) {
            return Objects.isNull(p0);
        }

        public Predicate__1() {
        }
    }

    private static final class Function__1 implements java.util.function.Function<java.lang.String, java.lang.Integer> {

        public java.lang.Integer apply(java.lang.String p0) {
            return p0.length();
        }

        public Function__1() {
        }
    }

    private static final class Predicate__2 implements java.util.function.Predicate<java.lang.String> {

        public boolean test(java.lang.String arg0) {
            return this._outer_final_s.isEmpty();
        }

        private final String _outer_final_s;

        public Predicate__2(String s) {
            this._outer_final_s = s;
        }
    }

    private static final class Function__2 implements java.util.function.Function<java.lang.Integer, LambdaMethodRef.Box> {

        public LambdaMethodRef.Box apply(java.lang.Integer p0) {
            return new Box(p0);
        }

        public Function__2() {
        }
    }
}
