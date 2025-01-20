/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit;

import recoder.abstraction.ArrayType;
import recoder.abstraction.PrimitiveType;
import recoder.abstraction.Type;
import recoder.convenience.Naming;

/**
 * Generator for variable and method names creating an unbound series of names derived from short
 * cut versions of the base name or by enumeration. The generator can be configured for short style
 * (temporary variables) or long style (public names) naming schemes. The generator takes care that
 * no Java keywords are generated.
 *
 * @author AL
 */
public class NameGenerator {

    /**
     * Short style using the shortest forms only. Useful for local names.
     */
    public final static int SHORT_STYLE = -1;

    /**
     * Default style using short form for very long names only.
     */
    public final static int DEFAULT_STYLE = 0;

    /**
     * Long style attempting to closely match the original name.
     */
    public final static int LONG_STYLE = 1;
    /**
     * Attempt counter. Can grow up to infinity.
     */
    private int attempt = 0;
    /**
     * Array of derived candidates.
     */
    private String[] derivates;

    /**
     * Create a generator for names based on the given name using default style.
     *
     * @param base the base name.
     */
    public NameGenerator(String base) {
        this(base, DEFAULT_STYLE);
    }

    /**
     * Create a generator for names based on the given name and style.
     *
     * @param base the base name.
     * @param strategy the style to use.
     */
    public NameGenerator(String base, int strategy) {
        guessNames(base, strategy);
    }

    /**
     * Create a generator for names based on the given type name. Uses short style for primitive
     * types, default style otherwise.
     *
     * @param type the type to derive a name from.
     */
    public NameGenerator(Type type) {
        while (type instanceof ArrayType) {
            type = ((ArrayType) type).getBaseType();
        }
        if (type instanceof PrimitiveType) {
            guessNames(type.getName(), SHORT_STYLE);
        } else {
            guessNames(type.getName(), DEFAULT_STYLE);
        }
    }

    private static String[] getLetters(String base) {
        char c = Character.toLowerCase(base.charAt(0));
        if (c < 'y') {
            return new String[] { base, "" + (char) (c + 1), "" + (char) (c + 2) };
        }
        if (c < 'z') {
            return new String[] { base, "" + (char) (c + 1) };
        }
        return new String[] { base };
    }

    /**
     * Separates single words of a base string using the following rules: 1. the first letter
     * belongs to the first word 2. the last letter belongs to the last word 3. a capital letter
     * with an adjacent lower case letter or underscore starts a new word
     */
    private static String[] separateWords(String base) {
        int len = base.length();
        StringBuffer[] buf = new StringBuffer[len / 2];
        int w = 0;
        buf[w] = new StringBuffer();
        buf[w].append(base.charAt(0));
        int i;
        for (i = 1; i < len - 1; i += 1) {
            char c = base.charAt(i);
            if (Character.isUpperCase(c)) {
                char d = base.charAt(i - 1);
                char e = base.charAt(i + 1);
                if (Character.isLowerCase(e) || e == '_' || Character.isLowerCase(d)) {
                    w += 1;
                    buf[w] = new StringBuffer();
                    buf[w].append(c);
                    continue;
                }
            }
            buf[w].append(c);
        }
        buf[w].append(base.charAt(len - 1));
        String[] res = new String[w + 1];
        for (int j = 0; j <= w; j += 1) {
            res[j] = buf[j].toString();
        }
        return res;
    }

    private static boolean isVowel(char c) {
        c = Character.toLowerCase(c);
        return c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'y';
    }

    private static String removeVowels(String str) {
        int len = str.length();
        StringBuilder res = new StringBuilder(len);
        for (int i = 0; i < len; i += 1) {
            char c = str.charAt(i);
            if (!isVowel(c)) {
                res.append(c);
            }
        }
        return res.toString();
    }

    private static String[] deriveShortCuts(int index, String[] words) {
        String base = words[index];
        int len = base.length();
        String[] res = new String[6];
        int w = 0;
        char c0 = base.charAt(0);
        // if first letter is upper case, use lower case word
        if (Character.isUpperCase(c0)) {
            String s = base.toLowerCase();
            if (!Naming.isKeyword(s)) {
                res[w++] = s;
            }
        }
        if (len > 3) {
            // if length is at least 4 letters and second letter is not a
            // vowel, use first two letters
            char c1 = base.charAt(1);
            if (!isVowel(c1)) {
                String s = base.substring(0, 2).toLowerCase();
                if (!Naming.isKeyword(s)) {
                    res[w++] = s;
                }
            }
            // if length is at least 4(5) letters and first letter is not a
            // vowel, and removal of all vowels leads to a two(three) letters
            // word, use that word
            if (!isVowel(c0)) {
                String bs = removeVowels(base);
                if (bs.length() == 2 || (bs.length() == 3 && len > 4)) {
                    String s = bs.toLowerCase();
                    if (!Naming.isKeyword(s)) {
                        res[w++] = s;
                    }
                }
            }
            // if length is at least 5 letters and third letter is not a vowel,
            // use first three letters
            if (len > 4) {
                char c2 = base.charAt(2);
                if (!isVowel(c2)) {
                    String s = base.substring(0, 3).toLowerCase();
                    if (!Naming.isKeyword(s)) {
                        res[w++] = s;
                    }
                }
            }
        }
        // use the first letter in small case, unless it is equals the base
        char lc0 = Character.toLowerCase(c0);
        if (len > 1 || Character.isUpperCase(c0)) {
            String s = "" + lc0;
            if (!Naming.isKeyword(s)) {
                res[w++] = s;
            }
        }

        // sort by length and remove duplicates
        for (int i = 1; i < w; i += 1) {
            String x = res[i];
            int j = i - 1;
            int xlen = x.length();
            while (j >= 0 && res[j].length() > xlen) {
                res[j + 1] = res[j];
                j -= 1;
            }
            if (j >= 0 && res[j].equals(x)) {
                for (j += 1, w -= 1, i -= 1; j < len; j += 1) {
                    res[j] = res[j + 1];
                }
            } else {
                res[j + 1] = x;
            }
        }
        // copy to result and return
        String[] result = new String[w];
        System.arraycopy(res, 0, result, 0, w);
        return result;
    }

    /**
     * Returns the next name candidate.
     *
     * @return the next derivation of the base name.
     */
    public String getNextCandidate() {
        String res;
        if (attempt < derivates.length) {
            res = derivates[attempt];
        } else {
            res = derivates[0] + (2 + attempt - derivates.length);
        }
        attempt += 1;
        return res;
    }

    // combine words:
    // if there are too many of them (4+), use first, shortest candidates only
    // otherwise, go from long to short forms from left to right
    private void guessNames(String base, int strategy) {
        String[] words = separateWords(base);
        int len = words.length;
        if (strategy == DEFAULT_STYLE) {
            strategy = (len >= 4) ? SHORT_STYLE : LONG_STYLE;
        }
        String[][] shortCuts = new String[len][];
        for (int i = 0; i < len; i += 1) {
            shortCuts[i] = deriveShortCuts(i, words);
        }
        if (strategy == SHORT_STYLE) {
            StringBuilder res = new StringBuilder(len);
            for (int i = 0; i < len; i += 1) {
                res.append(shortCuts[i][0]);
            }
            if (len == 1) {
                derivates = getLetters(res.toString());
            } else {
                derivates = new String[] { res.toString() };
            }
        } else {
            int c = 1;
            for (int i = 0; i < len; i += 1) {
                c += shortCuts[i].length - 1;
            }
            derivates = new String[c];
            c = 0;
            for (int i = 0; i < len; i += 1) {
                for (int k = shortCuts[i].length - ((i == 0) ? 1 : 2); k >= 0; k -= 1) {
                    StringBuilder buf = new StringBuilder();
                    for (int j = 0; j < i; j += 1) {
                        buf.append(shortCuts[j][0]);
                    }
                    buf.append(shortCuts[i][k]);
                    for (int j = i + 1; j < len; j += 1) {
                        buf.append(words[j]);
                    }
                    derivates[c++] = buf.toString();
                }
            }
        }
    }

    /*
     * Test program public static void main(String[] a) { for (int j = 0; j < a.length; j += 1) {
     * System.out.print(a[j] + " -> "); NameGenerator nc = new NameGenerator(a[j], 0); for (int i =
     * 0; i < 10; i += 1) { System.out.print(nc.getNextCandidate() + " "); } System.out.println(); }
     * }
     */
}
