/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.java;

import java.util.Arrays;
import java.util.Comparator;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javax.swing.*;

import org.checkerframework.checker.nullness.qual.PolyNull;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * Provides static methods to work with strings.
 *
 * @author Martin Hentschel
 */
public final class StringUtil {
    /** Pattern for newlines */
    private static final Pattern NEWLINE_PATTERN = Pattern.compile("(\\r\\n|\\r|\\n)");

    /**
     * Constant for an empty string.
     */
    public static final String EMPTY_STRING = "";

    /**
     * Constant for a line break.
     */
    public static final String NEW_LINE = System.getProperty("line.separator");

    /**
     * The latin alphabet with big capitals.
     */
    public static final String LATIN_ALPHABET_BIG = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";

    /**
     * The latin alphabet with small capitals.
     */
    public static final String LATIN_ALPHABET_SMALL = LATIN_ALPHABET_BIG.toLowerCase();

    /**
     * Additional characters allowed in file systems.
     * <p>
     * It is important that {@code ':'} is not contained because {@code "::"} is replaced with a
     * {@code '/'} by the {@link JFileChooser} under Mac OS.
     */
    public static final char[] ADDITIONAL_ALLOWED_FILE_NAME_SYSTEM_CHARACTERS =
        { '(', ')', '[', ']', '-', '+', '_', '$', ',', '%' };

    /**
     * The numerals.
     */
    public static final String NUMERALS = "0123456789";

    /**
     * All characters representing whitespace.
     */
    public static final String WHITESPACE = " \n\r\t";


    static {
        Arrays.sort(ADDITIONAL_ALLOWED_FILE_NAME_SYSTEM_CHARACTERS);
    }

    /**
     * Forbid instances by this private constructor.
     */
    private StringUtil() {
    }

    /**
     * Checks if the {@link String} is empty.
     *
     * @param text The text to check.
     * @return {@code true} = text is {@code null} or empty, {@code false} = text is not empty.
     */
    public static boolean isEmpty(@Nullable String text) {
        return text == null || text.isEmpty();
    }

    /**
     * Checks if the trimmed {@link String} is empty.
     *
     * @param text The text to check.
     * @return {@code true} = text is {@code null} or trimmed empty, {@code false} = text is not
     *         empty.
     */
    public static boolean isTrimmedEmpty(@Nullable String text) {
        return text == null || text.trim().isEmpty();
    }

    /**
     * Nullpointer save execution of {@link String#trim()}
     *
     * @param text The text.
     * @return The trimmed text.
     */
    public static @Nullable String trim(@Nullable String text) {
        return text != null ? text.trim() : null;
    }

    /**
     * Nullpointer save execution of {@link String#toLowerCase()}.
     *
     * @param text The text to convert.
     * @return The text in lower case or {@code null} if the given text is {@code null}.
     */
    public static @PolyNull String toLowerCase(@PolyNull String text) {
        return text == null ? null : text.toLowerCase();
    }

    /**
     * Creates a {@link Comparator} that can be used to compute the equality of two given
     * {@link String}s ignoring the case via {@link String#compareToIgnoreCase(String)}. If both
     * values are {@code null} also {@code 0} is returned in
     * {@link Comparator#compare(Object, Object)}. If only one value is {@code null}
     * {@link Comparator#compare(Object, Object)} will return a value different to {@code 0}.
     *
     * @return The created {@link Comparator}.
     */
    public static Comparator<@Nullable String> createIgnoreCaseComparator() {
        return (o1, o2) -> {
            if (o1 != null && o2 != null) {
                return o1.compareToIgnoreCase(o2);
            } else {
                return o1 == null && o2 == null ? 0 : 1;
            }
        };
    }

    /**
     * Creates a line which consists of the given text.
     *
     * @param text The text to repeat.
     * @param repetitions The number of repetitions.
     * @return The created line.
     */
    public static String repeat(String text, int repetitions) {
        return text.repeat(repetitions);
    }

    /**
     * <p>
     * Checks if the given string contains the substring.
     * </p>
     * <p>
     * <b>Attention:</b> The empty string is contained in every string.
     * </p>
     *
     * @param string The string that should contain the substring.
     * @param substring The substring to check.
     * @return {@code true} strings are not {@code null} and the string contains the substring,
     *         {@code false} if at least one string is {@code null} or the string does not contain
     *         the substring.
     */
    public static boolean contains(@Nullable String string, @Nullable CharSequence substring) {
        return string != null && substring != null && string.contains(substring);
    }

    /**
     * Wrap lines in a string. It replaces ' ' by '\n' such that (in general) every line is at most
     * {@code length} characters long. If there are no spaces within {@code length} characters, then
     * the long strings will not be broken and lines may be longer.
     *
     * @param string the string to break. May contain spaces and newline characters
     * @param length a positive number
     * @return a string of the same length as the input in which some ' ' have been replaced by '\n'
     *
     * @author Mattias Ulbrich (under GPL)
     */
    public static @NonNull String wrapLines(@NonNull String string, int length) {
        char[] c = string.toCharArray();
        WrapUtils.wrapLines(c, length);
        return new String(c);
    }

    /**
     * Wrap lines in a string. It replaces ' ' by '\n' such that (in general) every line is at most
     * 100 characters long. If there are no spaces within 100 characters, then the long strings will
     * not be broken and lines may be longer.
     *
     * @param string the string to break. May contain spaces and newline characters
     * @return a string of the same length as the input in which some ' ' have been replaced by '\n'
     *
     * @author Mattias Ulbrich (under GPL)
     */
    public static @NonNull String wrapLines(@NonNull String string) {
        return wrapLines(string, 100);
    }

    /**
     * Converts the optional multi lined {@link String} in a single lined {@link String} by
     * replacing all line breaks and tabs with a space.
     *
     * @param text The text to convert.
     * @return The single lined text.
     */
    public static @Nullable String toSingleLinedString(@Nullable String text) {
        return replaceAll(text, new char[] { '\n', '\r', '\t' }, ' ');
    }

    /**
     * Replaces all occurrences of a search sign with the replacement sign.
     *
     * @param text The text to search and replace in.
     * @param toSearch The signs to search.
     * @param toReplace The sign to replace with.
     * @return The new created {@link String}.
     */
    public static @Nullable String replaceAll(@Nullable String text, char[] toSearch,
            char toReplace) {
        if (text != null && toSearch != null) {
            // Sort toSearch
            Arrays.sort(toSearch);
            // Create new String.
            char[] signs = text.toCharArray();
            for (int i = 0; i < signs.length; i++) {
                int index = Arrays.binarySearch(toSearch, signs[i]);
                if (index >= 0) {
                    signs[i] = toReplace;
                }
            }
            return new String(signs);
        } else {
            return text;
        }
    }

    /**
     * Checks the equality of the given {@link String}s ignoring whitespace.
     *
     * @param first The first {@link String}.
     * @param second The second {@link String}.
     * @return {@code true} equal ignoring whitespace, {@code false} different.
     */
    public static boolean equalIgnoreWhiteSpace(@Nullable String first, @Nullable String second) {
        if (first != null) {
            if (second != null) {
                char[] firstContent = first.toCharArray();
                char[] secondContent = second.toCharArray();
                int firstIndex = 0;
                int secondIndex = 0;
                // Skip initial whitespace
                while (firstIndex < firstContent.length
                        && contains(WHITESPACE, firstContent[firstIndex] + EMPTY_STRING)) {
                    firstIndex++;
                }
                while (secondIndex < secondContent.length
                        && contains(WHITESPACE, secondContent[secondIndex] + EMPTY_STRING)) {
                    secondIndex++;
                }
                // Start to compare content
                boolean equal = true;
                while (equal && firstIndex < firstContent.length
                        && secondIndex < secondContent.length) {
                    // Compare content
                    if (firstIndex < firstContent.length && secondIndex < secondContent.length) {
                        if (firstContent[firstIndex] != secondContent[secondIndex]) {
                            equal = false;
                        }
                    } else {
                        if (firstIndex < firstContent.length - 1
                                || secondIndex < secondContent.length - 1) {
                            equal = false;
                        }
                    }
                    firstIndex++;
                    secondIndex++;
                    // Skip whitespace
                    while (firstIndex < firstContent.length
                            && contains(WHITESPACE, firstContent[firstIndex] + EMPTY_STRING)) {
                        firstIndex++;
                    }
                    while (secondIndex < secondContent.length
                            && contains(WHITESPACE, secondContent[secondIndex] + EMPTY_STRING)) {
                        secondIndex++;
                    }
                }
                return equal && firstIndex >= firstContent.length
                        && secondIndex >= secondContent.length; // Complete content of both texts
                                                                // compared
            } else {
                return false;
            }
        } else {
            return second == null;
        }
    }

    /**
     * Fills the given text with the leading character until it has the defined length.
     *
     * @param text The text to fill.
     * @param leadingCharacter The leading character to use.
     * @param length The length to fill up to.
     * @return The created text.
     * @throws IllegalArgumentException If the text is already longer as the given length
     */
    public static @NonNull String fillString(@Nullable String text, char leadingCharacter,
            int length)
            throws IllegalArgumentException {
        StringBuilder sb = new StringBuilder();
        if (text != null) {
            if (text.length() > length) {
                throw new IllegalArgumentException(String.format(
                    "Text \"%s\" with length %d is longer as %d.", text, text.length(), length));
            } else {
                sb.append(String.valueOf(leadingCharacter).repeat(length - text.length()));
                sb.append(text);
            }
        } else {
            sb.append(String.valueOf(leadingCharacter).repeat(Math.max(0, length)));
        }
        return sb.toString();
    }

    /**
     * Performs a trim only on the right side.
     *
     * @param text The text to trim its right side.
     * @return The trimmed text.
     */
    public static @PolyNull String trimRight(@PolyNull String text) {
        if (text != null) {
            char[] content = text.toCharArray();
            int newLength = content.length;
            while (newLength >= 1 && Character.isWhitespace(content[newLength - 1])) {
                newLength--;
            }
            return newLength == text.length() ? text : text.substring(0, newLength);
        } else {
            return null;
        }
    }

    /**
     * Chops the given text if required.
     *
     * @param text The text to check.
     * @param maxLength The maximal length to ensure.
     * @return The text considering the maximal length.
     */
    public static @PolyNull String chop(@PolyNull String text, int maxLength) {
        if (text != null && text.length() > maxLength) {
            if (maxLength <= 0) {
                return EMPTY_STRING;
            } else if (maxLength == 1) {
                return ".";
            } else if (maxLength == 2) {
                return "..";
            } else if (maxLength == 3) {
                return "...";
            } else {
                return text.substring(0, maxLength - 3) + "...";
            }
        } else {
            return text;
        }
    }

    /**
     * Checks if the given {@link Object} is a {@link String} which starts with the given prefix.
     *
     * @param obj The {@link Object} to check.
     * @param prefix The prefix to check for.
     * @return {@code true} {@link Object} is {@link String} with given prefix, {@code false}
     *         otherwise.
     */
    public static boolean startsWith(@Nullable Object obj, @Nullable String prefix) {
        return obj instanceof String && prefix != null && ((String) obj).startsWith(prefix);
    }

    public static boolean isNumber(@NonNull String val) {
        try {
            Long.parseLong(val);
        } catch (NumberFormatException e) {
            return false;
        }
        return true;
    }


    /**
     * Returns a string that first and last characters violates the given predicate. Works similar
     * to {@link String#trim()} but allows to specify the characters that should be consider for
     * removal.
     *
     * The given predicate test the characters, if true the character is removed.
     */
    public static @NonNull String trim(@NonNull String text,
            @NonNull Predicate<Character> predicate) {
        int first = 0;
        int last = text.length() - 1;
        char[] value = text.toCharArray();

        while (first < last && predicate.test(value[first])) {
            ++first;
        }
        while (first <= last && predicate.test(value[last])) {
            --last;
        }
        return (first < last + 1) ? text.substring(first, last + 1) : "";
    }

    /**
     * Removes the given character {@code c} from the prefix/suffix of the given string.
     *
     * @see #trim(String, Predicate)
     */
    public static @NonNull String trim(@NonNull String text, char c) {
        return trim(text, it -> it == c);
    }

    /**
     * Removes the given characters (in {@code chars}) from the prefix/suffix of the given string.
     *
     * @see #trim(String, Predicate)
     */
    public static @NonNull String trim(@NonNull String text, @NonNull String chars) {
        return trim(text, it -> chars.indexOf(it) >= 0);
    }

    /**
     * Replaces newlines.
     *
     * @param text the text
     * @param with with
     * @return the normalized text.
     */
    public static @NonNull String replaceNewlines(@NonNull String text, String with) {
        return NEWLINE_PATTERN.matcher(text).replaceAll(with);
    }

    /**
     * Checks whether a string contains another one as a whole word (i.e., separated by whitespaces
     * or a semicolon at the end).
     *
     * @param s string to search in
     * @param word string to be searched for
     */
    public static boolean containsWholeWord(@NonNull String s, @NonNull String word) {
        Pattern p = Pattern.compile("\\b" + word + "\\b");
        Matcher m = p.matcher(s);
        return m.find();
        /*
         * if (s == null || word == null) { return false; } int i = -1; final int wl =
         * word.length(); while (true) { i = s.indexOf(word, i + 1); if (i < 0 || i >= s.length())
         * break; if (i == 0 || Character.isWhitespace(s.charAt(i - 1))) { if (i + wl == s.length()
         * || Character.isWhitespace(s.charAt(i + wl)) || s.charAt(i + wl) == ';') { return true; }
         * } } return false;
         */
    }

    /**
     * There are different kinds of JML markers. See Section 4.4 "Annotation markers" of the JML
     * reference manual.
     *
     * @param comment
     * @return
     */
    public static boolean isJMLComment(@NonNull String comment) {
        try {
            return (comment.startsWith("/*@") || comment.startsWith("//@")
                    || comment.startsWith("/*+KeY@") || comment.startsWith("//+KeY@")
                    || (comment.startsWith("/*-") && !comment.startsWith("KeY", 3)
                            && comment.contains("@"))
                    || (comment.startsWith("//-") && !comment.startsWith("KeY", 3)
                            && comment.contains("@")));
        } catch (IndexOutOfBoundsException e) {
            return false;
        }
    }

    /**
     * Count occurences of character x in text, starting at beginIndex and ending at endIndex
     * (exclusive).
     *
     * @param text text
     * @param beginIndex start index (inclusive)
     * @param endIndex end index (exclusive)
     * @param x character to search for
     * @return number of times x is present
     */
    public static int count(String text, int beginIndex, int endIndex, char x) {
        return (int) text.chars().skip(beginIndex).limit(endIndex - beginIndex)
                .filter(ch -> ch == x).count();
    }
}
