import java.util.Objects;
import java.util.function.Function;
import java.util.function.Predicate;

class LambdaMethodRef {

    static class Box {

        int size;

        /*@  
          @ requires size [@5,34:35='>=',<235>,9:26] 0;
          @ ensures this.size == size;

          @*/
        Box(int size) {
            this.size = size;
        }
    }

    static class Owner {

        int size;

        Owner(int size) {
            this.size = size;
        }

        /*@  
          @ ensures \result == this.size;

          @*/
        int sizeOf() {
            return size;
        }
    }

    /**
     * Functional interface with model methods; the target type of the constructor
     * reference {@code Box::new} below (Csiky 6.2.4 "Application: Method References").
     */
    interface BoxFactory {

        Box make(Integer size);

        //@ model booleanpreCondition(Integersize);
        /*@ model */ boolean preCondition(Integer size);

        //@ model two_state booleanpostCondition(Integersize,Box__result);
        /*@ model */ /*@ two_state */ boolean postCondition(Integer size, Box __result);
    }

    /**
     * Target type of the unbound instance method reference {@code Owner::sizeOf}.
     */
    interface IntGetter {

        Integer get(Owner owner);

        //@ model booleanpreCondition(Ownerowner);
        /*@ model */ boolean preCondition(Owner owner);

        //@ model two_state booleanpostCondition(Ownerowner,Integer__result);
        /*@ model */ /*@ two_state */ boolean postCondition(Owner owner, Integer __result);
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

    BoxFactory factory() {
        BoxFactory f = new BoxFactory__1();
        return f;
    }

    IntGetter unbound() {
        IntGetter g = new IntGetter__1();
        return g;
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

    private static final class BoxFactory__1 implements LambdaMethodRef.BoxFactory {

        public LambdaMethodRef.Box make(java.lang.Integer p0) {
            return new Box(p0);
        }

        public BoxFactory__1() {
        }

        //@ model booleanpreCondition(java.lang.Integerp0){returnp0 [@22,62:63='>=',<235>,2:61] 0;}
        /*@ model */ boolean preCondition(java.lang.Integer p0);

        //@ model two_state booleanpostCondition(java.lang.Integerp0,LambdaMethodRef.Box__result){return__result.size == p0;}
        /*@ model */ /*@ two_state */ boolean postCondition(java.lang.Integer p0, LambdaMethodRef.Box __result);
    }

    private static final class IntGetter__1 implements LambdaMethodRef.IntGetter {

        public java.lang.Integer get(LambdaMethodRef.Owner p0) {
            return p0.sizeOf();
        }

        public IntGetter__1() {
        }

        //@ model two_state booleanpostCondition(LambdaMethodRef.Ownerp0,java.lang.Integer__result){return__result == p0.size;}
        /*@ model */ /*@ two_state */ boolean postCondition(LambdaMethodRef.Owner p0, java.lang.Integer __result);
    }
}
