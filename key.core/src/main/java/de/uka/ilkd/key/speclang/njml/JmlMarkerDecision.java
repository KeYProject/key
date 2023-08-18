/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;

/**
 * Externalize algorithm to decide whether a JML comment is active given a set of enabled keys.
 *
 * @author Alexander Weigl
 * @version 1 (9/24/21)
 * @see #isComment(String)
 */
public class JmlMarkerDecision {
    private final JmlLexer lexer;
    private Set<String> enabledKeys = new HashSet<>();

    /**
     * Initialize this class with default {@code enabledKeys} of {@code "key"}.
     *
     * @param lexer a lexer instance which stream is used
     */
    public JmlMarkerDecision(JmlLexer lexer) {
        this.lexer = lexer;
        enabledKeys.add("key");
    }

    /**
     * Sets the enabled keys for the recognition of active JML comments. Keys are treated
     * case-insensitive.
     *
     * @param markers a collection of keys without prefix ([+-])
     */
    public void setEnabledKeys(@Nonnull Collection<String> markers) {
        this.enabledKeys = markers.stream().map(String::toLowerCase).collect(Collectors.toSet());
    }

    public Collection<String> getEnabledKeys() {
        return Collections.unmodifiableCollection(enabledKeys);
    }

    /**
     * Lookahead for determining if we are at the start of comment and not a "JML
     * expectedCommentStart".
     * <p>
     * This method reads from the input stream to check the annotation markers between the comment
     * start and the "@" This method returns true for expectedCommentStart "//" if we the comment
     * begins with
     * <ul>
     * <li>"//" + End-of-line
     * <li>"// "
     * <li>"// @"
     * <li>"//+"
     * <li>"//-"
     * <li>"//-key+openjml@" (or similar)
     * </ul>
     * <p>
     * (same for "/*")
     * <p>
     * It returns true if expectedCommentStart is followed by a sequence of "+", "-" or Java
     * identifier characters, and then "@" and the sequence does not contain "-key".
     * <p>
     * It implements JML Ref Manual 4.4: <quote> An annotation-key is a + or - sign followed by an
     * ident (see section 4.6 Tokens). Note that no white space can appear within, before, or after
     * the annotation-key. Tools will provide a way to enable a selection of annotation-key
     * identifiers. These identifiers, hereafter called "keys" provide for conditional inclusion of
     * JML annotations as follows:
     * <ul>
     * <li>a JML annotation with no keys is always included,
     * <li>a JML annotation with at least one positive-key is only included if at least one of these
     * positive keys is enabled and there are no negative-keys in the annotation that have enabled
     * keys, and
     * <li>a JML annotation with an enabled negative-key is ignored (even if there are enabled
     * positive-keys).
     * </ul>
     * </quote>
     * <p>
     * This method resets the position on the input stream (mark/rewind).
     *
     * @return true if lexer is at a comment, and not in front of a JML specification.
     */
    public boolean isComment(String expectedCommentStart) {
        int mark = lexer._input.mark();
        int startPos = lexer._input.index();

        try {
            // matching the expected start of the comment
            if (consume(expectedCommentStart)) {
                return false;
            }

            // consume until '@' is hit, or else it is not a JML comment
            StringBuilder markerBuilder = new StringBuilder();
            while (true) {
                final char point = (char) lexer._input.LA(1);
                if (point == '@') { // annotation marker finished
                    return !isActiveJmlSpec(markerBuilder.toString());
                } else if (Character.isJavaIdentifierPart(point) || point == '-' || point == '+') {
                    markerBuilder.append(point);
                    lexer._input.consume();
                } else {
                    return true;
                }
            }
        } finally {
            lexer._input.seek(startPos);
            lexer._input.release(mark);
        }
    }

    private boolean consume(String str) {
        for (int i = 0; i < str.length(); i++) {
            if (lexer._input.LA(1) == str.charAt(i)) {
                lexer._input.consume();
            } else {
                return true;
            }
        }
        return false;
    }

    public boolean isActiveJmlSpec(String foundKeys) {
        if (foundKeys.isEmpty()) {
            // a JML annotation with no keys is always included,
            return true;
        }

        String[] keys = foundKeys.split("(?=[+-])");

        // a JML annotation with at least one positive-key is only included
        boolean plusKeyFound = false;
        // if at least one of these positive keys is enabled
        boolean enabledPlusKeyFound = false;

        // a JML annotation with an enabled negative-key is ignored (even if there are enabled
        // positive-keys).
        boolean enabledNegativeKeyFound = false;

        for (String marker : keys) {
            plusKeyFound = plusKeyFound || isPositive(marker);
            enabledPlusKeyFound = enabledPlusKeyFound || isPositive(marker) && isEnabled(marker);
            enabledNegativeKeyFound =
                enabledNegativeKeyFound || isNegative(marker) && isEnabled(marker);
            if ("-".equals(marker) || "+".equals(marker)) {
                return false;
            }
        }

        return (!plusKeyFound || enabledPlusKeyFound) && !enabledNegativeKeyFound;
    }

    private boolean isNegative(String marker) {
        return marker.charAt(0) == '-';
    }

    private boolean isEnabled(String marker) {
        // remove [+-] prefix
        return enabledKeys.contains(marker.substring(1).toLowerCase());
    }

    private boolean isPositive(String marker) {
        return marker.charAt(0) == '+';
    }
}
