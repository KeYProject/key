package java.util;

/**
 * Minimal boot stub of {@code java.util.Objects}: only the static methods used by
 * the lambda fixtures (symbol resolution).
 */
public class Objects {

    public static boolean isNull(Object obj) {
        return obj == null;
    }

    public static boolean nonNull(Object obj) {
        return obj != null;
    }

    public static Object requireNonNull(Object obj) {
        if (obj == null) {
            throw new NullPointerException();
        }
        return obj;
    }
}
