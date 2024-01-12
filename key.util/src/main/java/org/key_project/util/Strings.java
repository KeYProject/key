/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;


import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

/**
 * Helper functions for {@link String}s
 *
 * @author Alexander Weigl
 * @version 1 (29.03.19)
 */
public class Strings {
    /**
     * Checks whether a string contains another one as a whole word (i.e., separated by whitespaces
     * or a semicolon at the end).
     *
     * @param s string to search in
     * @param word string to be searched for
     */
    public static boolean containsWholeWord(String s, String word) {
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
    public static boolean isJMLComment(String comment) {
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
     * outputs the collection represented by the iterator in the format
     * <code> open element1 sep element2 sep element3 close</code>
     *
     * @param it the Iterable to be printed
     * @param open the String used to open the list
     * @param sep the String separating the different elements
     * @param close the String used to close the list
     * @param mapper a Function that maps the elements of type S to their String representation
     * @return the CharSequence in the described format
     * @param <S> the type of the elements of the iterated collection
     */
    public static <S, T> String formatAsList(Iterable<S> it,
            CharSequence open, CharSequence sep, CharSequence close,
            Function<S, T> mapper) {
        return StreamSupport.stream(it.spliterator(), false)
                .map(a -> mapper.apply(a).toString())
                .collect(Collectors.joining(sep, open, close));
    }

    /**
     * outputs the collection represented by the iterator in the format
     * <code> open element1 sep element2 sep element3 close</code>
     *
     * @param it the Iterable to be printed
     * @param open the String used to open the list
     * @param sep the String separating the different elements
     * @param close the String used to close the list
     * @return the CharSequence in the described format
     * @param <S> the type of the elements of the iterated collection
     */
    public static <S> String formatAsList(Iterable<S> it,
            CharSequence open, CharSequence sep, CharSequence close) {
        return formatAsList(it, open, sep, close, Function.identity());
    }
}
