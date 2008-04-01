

package java.lang;

public final class Double extends Number implements Comparable {
    public static final double MAX_VALUE = 1.7976931348623157e+308;
    public static final double MIN_VALUE = 5e-324;
    public static final double NEGATIVE_INFINITY = -1.0 / 0.0;
    public static final double POSITIVE_INFINITY = 1.0 / 0.0;
    public static final double NaN = 0.0 / 0.0;
    static {}
    public Double(double value) {}
    public Double(String s) {}
    public static String toString(double d) {}
    public static Double valueOf(String s) {}
    public static native double parseDouble(String str);
    public static boolean isNaN(double v) {}
    public static boolean isInfinite(double v) {}
    public boolean isNaN() {}
    public boolean isInfinite() {}
    public String toString() {}
    public byte byteValue() {}
    public short shortValue() {}
    public int intValue() {}
    public long longValue() {}
    public float floatValue() {}
    public double doubleValue() {}
    public int hashCode() {}
    public boolean equals(Object obj) {}
    public static long doubleToLongBits(double value) {}
    public static long doubleToRawLongBits(double value) {}
    public static double longBitsToDouble(long bits) {}
    public int compareTo(Double d) {}
    public int compareTo(Object o) {}
    public static int compare(double x, double y) {}
    static native String toString(double d, boolean isFloat);
    private static native void initIDs();
}
