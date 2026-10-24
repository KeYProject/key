import java.util.Objects;

class LambdaPredicate {

    private final int test;

    public LambdaPredicate() {
        this.test = 1;
    }

    void m(int i) {
        int outer = 10;
        final class Predicate__1 implements LambdaPredicate.Predicate<java.lang.Integer> {

            public boolean test(java.lang.Integer a) {
                return a > 10;
            }
        }
        Predicate<Integer> tester = new Predicate__1();
        tester.test(outer);
    }

    @FunctionalInterface
    public interface Predicate<T> {

        boolean test(T var1);

        default Predicate<T> and(Predicate<? super T> var1) {
            Objects.requireNonNull(var1);
            final class Predicate__2 implements LambdaPredicate.Predicate {

                public boolean test(java.lang.Object var2) {
                    return Predicate.this.test(var2) && var1.test(var2);
                }
            }
            return new Predicate__2();
        }

        default Predicate<T> negate() {
            final class Predicate__3 implements LambdaPredicate.Predicate {

                public boolean test(java.lang.Object var1) {
                    return !Predicate.this.test(var1);
                }
            }
            return new Predicate__3();
        }

        default Predicate<T> or(Predicate<? super T> var1) {
            Objects.requireNonNull(var1);
            final class Predicate__4 implements LambdaPredicate.Predicate {

                public boolean test(java.lang.Object var2) {
                    return Predicate.this.test(var2) || var1.test(var2);
                }
            }
            return new Predicate__4();
        }

        static <T> Predicate<T> isEqual(Object var0) {
            if (var0 == null) {
                final class Predicate__5 implements LambdaPredicate.Predicate {

                    public boolean test(java.lang.Object var1) {
                        return var1 == null;
                    }
                }
                return new Predicate__5();
            }
            final class Predicate__6 implements LambdaPredicate.Predicate {

                public boolean test(java.lang.Object var1) {
                    return var0.equals(var1);
                }
            }
            return new Predicate__6();
        }
    }
}
