


package java.lang;
public final class Long extends Number implements Comparable {
    public static final long MIN_VALUE = 0x8000000000000000L;
    public static final long MAX_VALUE = 0x7fffffffffffffffL;
    public Long(long value) {}
    public Long(String s) {}
    public static String toString(long num, int radix) {}
    public static String toHexString(long l) {}
    public static String toOctalString(long l) {}
    public static String toBinaryString(long l) {}
    public static String toString(long num) {}
    public static long parseLong(String str, int radix) {}
    public static long parseLong(String s) {}
    public static Long valueOf(String s, int radix) {}
    public static Long valueOf(String s) {}
    public static Long decode(String str) {}
    public byte byteValue() {}
    public short shortValue() {}
    public int intValue() {}
    public long longValue() {}
    public float floatValue() {}
    public double doubleValue() {}
    public String toString() {}
    public int hashCode() {}
    public boolean equals(Object obj) {}
    public static Long getLong(String nm) {}
    public static Long getLong(String nm, long val) {}
    public static Long getLong(String nm, Long def) {}
    public int compareTo(Long l) {}
    public int compareTo(Object o) {}
    private static String toUnsignedString(long num, int exp) {}
    private static long parseLong(String str, int radix, boolean decode) {}
}
