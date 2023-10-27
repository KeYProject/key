/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;

import org.key_project.util.java.StringUtil;

import org.jspecify.annotations.NullMarked;

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
@NullMarked
public class Strings {
    /**
     * @deprecated This class has been merged with {@link org.key_project.util.java.StringUtil}.
     *             Call
     *             {@link org.key_project.util.java.StringUtil#containsWholeWord(String, String)}
     */
    @Deprecated
    public static boolean containsWholeWord(String s, String word) {
        return StringUtil.containsWholeWord(s, word);
    }

    /**
     * @deprecated This class has been merged with {@link org.key_project.util.java.StringUtil}.
     *             Call {@link org.key_project.util.java.StringUtil#isJMLComment(String)}
     */
    @Deprecated
    public static boolean isJMLComment(String comment) {
        return StringUtil.isJMLComment(comment);
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
