/**
 * Example demonstrating Java 21+ record patterns in KeY.
 *
 * A record pattern deconstructs a record value and binds its components:
 *
 *   if (obj instanceof Point(int x, int y)) {
 *       // x and y are bound to obj.x() and obj.y()
 *   }
 *
 * Record patterns nest, so whole object graphs can be matched and destructured in one
 * expression.
 */
public class RecordPatternExample {
    record Point(int x, int y) { }
    record Line(Point start, int length) { }
    record Box(Object value) { }

    static class Animal { }
    static class Dog extends Animal { }

    record DogBox(Dog value) { }

    /*@ normal_behavior
      @ requires true;
      @ ensures \result >= 0;
      @*/
    public static int sum(Object o) {
        if (o instanceof Point(int x, int y)) {
            if (x >= 0 && y >= 0) {
                return x + y;
            }
        }
        return 0;
    }

    /*@ normal_behavior
      @ requires true;
      @ ensures \result >= 0;
      @*/
    public static int nested(Object o) {
        if (o instanceof Line(Point(int x, int y), int length)) {
            if (x >= 0 && y >= 0 && length >= 0) {
                return x + y + length;
            }
        }
        return 0;
    }

    /*@ normal_behavior
      @ requires true;
      @ ensures \result == 0 || \result == 1;
      @*/
    public static int conditional(Object o) {
        if (o instanceof Box(String value)) {
            return 1;
        }
        return 0;
    }

    /*@ normal_behavior
      @ requires true;
      @ ensures \result == 0 || \result > 0;
      @*/
    public static int compound(Object o) {
        boolean positive;
        positive = o instanceof Point(int x, int y) && x > 0 && y > 0;
        return positive ? 1 : 0;
    }

    /*@ normal_behavior
      @ requires true;
      @ ensures \result == true;
      @*/
    public static boolean nullMatchingComponent() {
        // JLS 14.30.1: Object is unconditional for an Object component, so the pattern also
        // matches a null component.
        return (new Box(null)) instanceof Box(Object value);
    }

    /*@ normal_behavior
      @ requires true;
      @ ensures \result == true;
      @*/
    public static boolean nullMatchingVar() {
        // 'var' infers the component's declared type (Object), which is unconditional for it.
        return (new Box(null)) instanceof Box(var value);
    }

    /*@ normal_behavior
      @ requires true;
      @ ensures \result == true;
      @*/
    public static boolean nullMatchingSupertype() {
        // Animal is a supertype of the Dog component: every non-null Dog matches it,
        // and null does as well.
        return (new DogBox(null)) instanceof DogBox(Animal value);
    }
}
