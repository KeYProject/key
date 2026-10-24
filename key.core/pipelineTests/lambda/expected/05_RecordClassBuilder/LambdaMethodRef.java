import java.util.Objects;
import java.util.function.Function;
import java.util.function.Predicate;

class LambdaMethodRef {

    static class Box {

        Box(int size) {
        }
    }

    Predicate<Object> nullTest() {
        Predicate<Object> p = Objects::isNull;
        return p;
    }

    Function<String, Integer> length() {
        Function<String, Integer> f = String::length;
        return f;
    }

    Predicate<String> bounded() {
        String s = "abc";
        Predicate<String> p = s::isEmpty;
        return p;
    }

    Function<Integer, Box> factory() {
        Function<Integer, Box> f = Box::new;
        return f;
    }
}
