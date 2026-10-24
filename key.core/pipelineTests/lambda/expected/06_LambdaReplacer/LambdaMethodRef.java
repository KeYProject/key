import java.util.Objects;
import java.util.function.Function;
import java.util.function.Predicate;

class LambdaMethodRef {

    static class Box {

        Box(int size) {
        }
    }

    Predicate<Object> nullTest() {
        final class Predicate__1 implements java.util.function.Predicate<java.lang.Object> {

            public boolean test(java.lang.Object p0) {
                return Objects.isNull(p0);
            }
        }
        Predicate<Object> p = new Predicate__1();
        return p;
    }

    Function<String, Integer> length() {
        final class Function__1 implements java.util.function.Function<java.lang.String, java.lang.Integer> {

            public java.lang.Integer apply(java.lang.String p0) {
                return p0.length();
            }
        }
        Function<String, Integer> f = new Function__1();
        return f;
    }

    Predicate<String> bounded() {
        String s = "abc";
        final class Predicate__2 implements java.util.function.Predicate<java.lang.String> {

            public boolean test(java.lang.String arg0) {
                return s.isEmpty();
            }
        }
        Predicate<String> p = new Predicate__2();
        return p;
    }

    Function<Integer, Box> factory() {
        final class Function__2 implements java.util.function.Function<java.lang.Integer, LambdaMethodRef.Box> {

            public LambdaMethodRef.Box apply(java.lang.Integer p0) {
                return new Box(p0);
            }
        }
        Function<Integer, Box> f = new Function__2();
        return f;
    }
}
