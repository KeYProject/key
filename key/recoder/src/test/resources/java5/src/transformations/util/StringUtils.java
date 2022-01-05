// This file is part of the RECODER library and protected by the LGPL

package recoder.util;

import java.util.StringTokenizer;

/**
 * This class contains convenience methods for string handling.
 * 
 * @author RN
 * @author UA
 * @author AL
 * @since 0.5
 */
public class StringUtils {

    private static int tmpStrCount = 0;

    private static String[] tmpStrs = new String[64];

    private static void initTmpStrs() {
        for (int i = tmpStrs.length - 1; i >= 0; i--) {
            tmpStrs[i] = null;
        }
        tmpStrCount = 0;
    }

    private static void addTmpStr(String s) {
        if (tmpStrCount == tmpStrs.length) {
            // double the array
            int c = tmpStrCount;
            String[] newVal = new String[c * 2];
            System.arraycopy(tmpStrs, 0, newVal, 0, c);
            initTmpStrs();
            tmpStrs = newVal;
            tmpStrCount = c;
        }
        tmpStrs[tmpStrCount++] = s;
    }

    private static String[] getTmpStrVals() {
        String[] res = new String[tmpStrCount];
        System.arraycopy(tmpStrs, 0, res, 0, tmpStrCount);
        return res;
    }

    /**
     * Splits the given string using the specified separator character.
     */
    public static synchronized String[] split(String str, char separator) {
        if (str == null) {
            return null;
        }
        initTmpStrs();
        String hs;
        int start = 0;
        int idx = str.indexOf(separator, start);
        while (idx != -1) {
            hs = str.substring(start, idx);
            addTmpStr(hs);
            start = idx + 1;
            idx = str.indexOf(separator, start);
        }
        hs = str.substring(start);
        addTmpStr(hs);
        return getTmpStrVals();
    }

    /**
     * Normalize a name without suffix
     */
    public static String basename(String s) {
        int lastIndex = s.lastIndexOf(java.io.File.separator);
        if (lastIndex == -1)
            return s;
        return s.substring(lastIndex + 1);
    }

    /**
     * Normalize a name without dot-suffix
     */
    public static String basenameDot(String s) {
        int lastIndex = s.lastIndexOf(".");
        if (lastIndex == -1)
            return s;
        return s.substring(lastIndex + 1);
    }

    /**
     * Normalize a name without directory prefix
     */
    public static String cutSuffix(String s) {
        int lastIndex = s.lastIndexOf(".");
        if (lastIndex == -1)
            return s;
        return s.substring(0, lastIndex);
    }

    /**
     * Cut off a prefix of a dotted name string.
     */
    public static String cutPrefix(String s) {
        int firstIndex = s.indexOf('.', 0);
        if (firstIndex == -1)
            return null;
        return s.substring(firstIndex + 1);
    }

    /**
     * Normalize a string without enclosing double quotes.
     */
    public static String removeDoubleQuotes(String s) {
        int firstIndex = s.indexOf("\"");
        int lastIndex = s.lastIndexOf("\"");
        if (lastIndex == -1 && firstIndex == -1)
            return s; // none in.
        if (lastIndex == firstIndex)
            return s; // one in.
        return s.substring(firstIndex + 1, lastIndex);
    }

    /**
     * Return a prefix of a dotted name string.
     */
    public static String getPrefix(String s) {
        int firstIndex = s.indexOf('.', 0);
        if (firstIndex == -1)
            return null;
        return s.substring(0, firstIndex);
    }

    /**
     * Return a suffix of a dotted name string.
     */
    public static String getSuffix(String s) {
        int lastIndex = s.lastIndexOf(".");
        if (lastIndex == -1)
            return null;
        return s.substring(lastIndex + 1, s.length());
    }

    /**
     * Return a modified class name with a new prefix of basename. (pp,x.y.z)
     * ==> x.y.ppz or (pp,z) ==> ppz
     */
    public static String prependNameToSuffix(String prepend, String s) {
        String newBaseName;
        String prefix = StringUtils.cutSuffix(s);
        String suffix = StringUtils.getSuffix(s);
        if (suffix == null) {
            // this was a simple class name without dot, no full class name
            newBaseName = prepend + s;
        } else {
            // full dotted class name
            newBaseName = prefix + "." + prepend + suffix;
        }
        return newBaseName;
    }

    /**
     * Replace the first occurence of pattern in from by replacement.
     */
    public static String stringReplace(String from, String pattern, String replacement) {
        int beginIndex = from.indexOf(pattern);
        String first = from.substring(0, beginIndex);
        first = first.concat(replacement);
        first = first.concat(from.substring(beginIndex + pattern.length()));
        return first;
    }

    /**
     * Transform a String[] to a string, separated by blanks.
     */
    public static String stringArray2String(String[] argv) {
        String returnString = "";
        for (int i = 0; i < argv.length; i++) {
            returnString = returnString + argv[i];
            if (i <= argv.length - 1) {
                returnString = returnString + " ";
            }
        }
        return returnString;
    }

    /**
     * Parse a String to a String[]. Delimiter are blanks.
     */
    public static String[] string2StringArray(String s) {
        StringTokenizer tokenizer = new StringTokenizer(s, " ");
        int tokenCount = tokenizer.countTokens();
        String[] returnArray = new String[tokenCount + 1];
        if (tokenCount == 0)
            return returnArray;

        int i = 0;
        while (tokenizer.hasMoreTokens()) {
            // lookup token as property, i.e. variable keyword.
            returnArray[i] = tokenizer.nextToken(" ");
            i++;
        }
        return returnArray;
    }

    /**
     * Interprets the given property as a boolean setting and returns the
     * result. Allowed values are "true", "T", "yes" or "1", and "false", "F",
     * "yes" or "0" respectively. Case is ignored, so "True" or "f" would also
     * considered valid.
     * 
     * @param str
     *            the property value.
     * @return the value of the property, interpreted as a boolean.
     * @exception IllegalArgumentException
     *                if the value cannot be interpreted.
     */
    public static boolean parseBooleanProperty(String str) {
        if (str.equalsIgnoreCase("true"))
            return true;
        if (str.equalsIgnoreCase("false"))
            return false;
        if (str.equalsIgnoreCase("t"))
            return true;
        if (str.equalsIgnoreCase("f"))
            return false;
        if (str.equalsIgnoreCase("yes"))
            return true;
        if (str.equalsIgnoreCase("no"))
            return false;
        if (str.equals("1"))
            return true;
        if (str.equals("0"))
            return false;
        throw new IllegalArgumentException(str + " cannot be interpreted as boolean value");
    }

}