/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.transformations.pipeline.lambda;

import java.util.ArrayList;
import java.util.List;
import java.util.function.UnaryOperator;

/**
 * Textual helpers for the clause bodies of lambda contracts (Csiky's thesis, Def. 8 "cb").
 * <p>
 * A clause body is raw source text extracted from a JML comment. Before it can be turned
 * into a model method on the desugared class, identifiers must be rewritten: parameter
 * names of a method reference target (Def. 8, "Application: Method References"), the
 * result placeholder {@code \result}, escape keywords {@code this}/{@code super}, and free
 * variables of the enclosing scope (which become fields of the desugared class).
 * <p>
 * This class splits a clause body into identifier-like tokens and verbatim text and marks
 * each identifier with its syntactic neighborhood (preceding/following dot, following
 * parenthesis), so that the callers can decide locally which tokens to substitute.
 *
 * @author weigl
 */
public final class ClauseText {

    private ClauseText() {
    }

    /**
     * An identifier-like token of a clause body together with its syntactic neighborhood.
     *
     * @param text the token text, including the leading {@code \} of JML escapes (e.g.
     *        {@code \result}) but without any surrounding whitespace
     * @param identifier whether this part is an identifier-like token (as opposed to verbatim
     *        operator/whitespace text)
     * @param prevDot is the preceding non-whitespace character a {@code .} (a qualified
     *        name component, e.g. {@code PI} in {@code Math.PI} or {@code this} in
     *        {@code Outer.this})
     * @param nextDot is the following non-whitespace character a {@code .} (a receiver or
     *        type name, e.g. {@code Math} in {@code Math.PI} or {@code x} in {@code x.y})
     * @param nextParen is the following non-whitespace character a {@code (} (a method or
     *        operator name, e.g. {@code abs} in {@code Math.abs(x)})
     */
    public record Part(String text, boolean identifier, boolean prevDot, boolean nextDot,
            boolean nextParen) {
    }

    /**
     * Splits {@code source} into identifier-like tokens and verbatim text.
     */
    public static List<Part> parts(String source) {
        List<Part> result = new ArrayList<>();
        int i = 0;
        int n = source.length();
        while (i < n) {
            if (isIdentStart(source.charAt(i))) {
                int end = i + 1;
                while (end < n && isIdentPart(source.charAt(end))) {
                    end++;
                }
                result.add(new Part(source.substring(i, end), true, prevDot(source, i),
                    nextDot(source, end), nextParen(source, end)));
                i = end;
            } else if (source.charAt(i) == '\\' && i + 1 < n
                    && isIdentStart(source.charAt(i + 1))) {
                // JML escape identifier: \result, \old, \nothing, ...
                int end = i + 2;
                while (end < n && isIdentPart(source.charAt(end))) {
                    end++;
                }
                String text = source.substring(i, end);
                result.add(
                    new Part(text, true, prevDot(source, i), nextDot(source, end),
                        nextParen(source, end)));
                i = end;
            } else {
                int end = i + 1;
                while (end < n && !isIdentStart(source.charAt(end))
                        && !(source.charAt(end) == '\\' && end + 1 < n
                                && isIdentStart(source.charAt(end + 1)))) {
                    end++;
                }
                result.add(new Part(source.substring(i, end), false, source.charAt(i) == '.', false,
                    false));
                i = end;
            }
        }
        return result;
    }

    /**
     * Applies {@code mapper} to every identifier token that is not a qualified-name component
     * (i.e. not preceded by a dot) and returns the resulting text. A {@code null} return keeps
     * the token verbatim.
     */
    public static String rewrite(String source, UnaryOperator<String> mapper) {
        StringBuilder sb = new StringBuilder();
        for (Part p : parts(source)) {
            if (p.identifier() && !p.prevDot()) {
                String rep = mapper.apply(p.text());
                sb.append(rep == null ? p.text() : rep);
            } else {
                sb.append(p.text());
            }
        }
        return sb.toString();
    }

    private static boolean prevDot(String source, int begin) {
        for (int i = begin - 1; i >= 0; i--) {
            char c = source.charAt(i);
            if (!Character.isWhitespace(c)) {
                return c == '.';
            }
        }
        return false;
    }

    private static boolean nextDot(String source, int end) {
        for (int i = end; i < source.length(); i++) {
            char c = source.charAt(i);
            if (!Character.isWhitespace(c)) {
                return c == '.';
            }
        }
        return false;
    }

    private static boolean nextParen(String source, int end) {
        for (int i = end; i < source.length(); i++) {
            char c = source.charAt(i);
            if (!Character.isWhitespace(c)) {
                return c == '(';
            }
        }
        return false;
    }

    private static boolean isIdentStart(char c) {
        return Character.isJavaIdentifierStart(c);
    }

    private static boolean isIdentPart(char c) {
        return Character.isJavaIdentifierPart(c) || c == '$';
    }
}
