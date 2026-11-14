import java.util.Objects;
import java.util.function.Function;
import java.util.function.Predicate;

class LambdaMethodRef {
    static class Box {
        int size;

        //@ requires size >= 0;
        //@ ensures this.size == size;
        Box(int size) {
            this.size = size;
        }
    }

    static class Owner {
        int size;

        Owner(int size) {
            this.size = size;
        }

        //@ ensures \result == this.size;
        int sizeOf() {
            return size;
        }
    }

    /**
     * Functional interface with model methods; the target type of the constructor
     * reference {@code Box::new} below (Csiky 6.2.4 "Application: Method References").
     */
    interface BoxFactory {
        //@ model boolean preCondition(Integer size);
        //@ model two_state boolean postCondition(Integer size, Box __result);
        Box make(Integer size);
    }

    /** Target type of the unbound instance method reference {@code Owner::sizeOf}. */
    interface IntGetter {
        //@ model boolean preCondition(Owner owner);
        //@ model two_state boolean postCondition(Owner owner, Integer __result);
        Integer get(Owner owner);
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

    BoxFactory factory() {
        BoxFactory f = Box::new;
        return f;
    }

    IntGetter unbound() {
        IntGetter g = Owner::sizeOf;
        return g;
    }
}