


package java.lang;


import java.io.CharConversionException;
import java.io.Serializable;
import java.io.UnsupportedEncodingException;
import java.util.Comparator;
import java.util.Locale;
import java.util.regex.Pattern;
public final class String implements Serializable, Comparable, CharSequence {
    final char[] value;
    final int count;
    final int offset;
    private static final class CaseInsensitiveComparator
     implements Comparator, Serializable {
        CaseInsensitiveComparator() {}
        public int compare(Object o1, Object o2) {}
    }
    public static final Comparator CASE_INSENSITIVE_ORDER = new CaseInsensitiveComparator();
    public String() {}
    public String(String str) {}
    public String(char[] data) {}
    public String(char[] data, int offset, int count) {}
    public String(byte[] ascii, int hibyte, int offset, int count) {}
    public String(byte[] ascii, int hibyte) {}
    public String(byte[] data, int offset, int count, String encoding) throws UnsupportedEncodingException {}
    public String(byte[] data, String encoding) throws UnsupportedEncodingException {}
    public String(byte[] data, int offset, int count) {}
    public String(byte[] data) {}
    public String(StringBuffer buffer) {}
    String(char[] data, int offset, int count, boolean dont_copy) {}
    public int length() {}
    public char charAt(int index) {}
    public void getChars(int srcBegin, int srcEnd, char dst[], int dstBegin) {}
    public void getBytes(int srcBegin, int srcEnd, byte dst[], int dstBegin) {}
    public byte[] getBytes(String enc) throws UnsupportedEncodingException {}
    public byte[] getBytes() {}
    public boolean equals(Object anObject) {}
    public boolean contentEquals(StringBuffer buffer) {}
    public boolean equalsIgnoreCase(String anotherString) {}
    public int compareTo(String anotherString) {}
    public int compareTo(Object o) {}
    public int compareToIgnoreCase(String str) {}
    public boolean regionMatches(int toffset, String other, int ooffset, int len) {}
    public boolean regionMatches(boolean ignoreCase, int toffset,
                               String other, int ooffset, int len) {}
    public boolean startsWith(String prefix, int toffset) {}
    public boolean startsWith(String prefix) {}
    public boolean endsWith(String suffix) {}
    public int hashCode() {}
    public int indexOf(int ch) {}
    public int indexOf(int ch, int fromIndex) {}
    public int lastIndexOf(int ch) {}
    public int lastIndexOf(int ch, int fromIndex) {}
    public int indexOf(String str) {}
    public int indexOf(String str, int fromIndex) {}
    public int lastIndexOf(String str) {}
    public int lastIndexOf(String str, int fromIndex) {}
    public String substring(int begin) {}
    public String substring(int beginIndex, int endIndex) {}
    public CharSequence subSequence(int begin, int end) {}
    public String concat(String str) {}
    public String replace(char oldChar, char newChar) {}
    public boolean matches(String regex) {}
    public String replaceFirst(String regex, String replacement) {}
    public String replaceAll(String regex, String replacement) {}
    public String[] split(String regex, int limit) {}
    public String[] split(String regex) {}
    public String toLowerCase(Locale loc) {}
    public String toLowerCase() {}
    public String toUpperCase(Locale loc) {}
    public String toUpperCase() {}
    public String trim() {}
    public String toString() {}
    public char[] toCharArray() {}
    public static String valueOf(Object obj) {}
    public static String valueOf(char[] data) {}
    public static String valueOf(char[] data, int offset, int count) {}
    public static String copyValueOf(char[] data, int offset, int count) {}
    public static String copyValueOf(char[] data) {}
    public static String valueOf(boolean b) {}
    public static String valueOf(char c) {}
    public static String valueOf(int i) {}
    public static String valueOf(long l) {}
    public static String valueOf(float f) {}
    public static String valueOf(double d) {}
    public String intern() {}
    private static int upperCaseExpansion(char ch) {}
    private static int upperCaseIndex(char ch) {}
    static char[] zeroBasedStringValue(String s) {}
}
