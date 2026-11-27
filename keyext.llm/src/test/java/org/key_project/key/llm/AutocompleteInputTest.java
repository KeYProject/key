/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Tests the expandable-fragment detection for the Ctrl+Space inline expansion of {@code $tokens},
 * {@code @file} references and {@code /directives} (see {@link AutocompleteInput}).
 */
class AutocompleteInputTest {

    private static String atCaret(String text) {
        return AutocompleteInput.tokenFragmentAtCaret(text, text.length());
    }

    @Test
    void dollarTokensAreDetected() {
        assertEquals("$seq", atCaret("analysing $seq"));
        assertEquals("$seq", atCaret("$seq"));
        assertEquals("$selectedFiles", atCaret("explain ($selectedFiles"));
        assertEquals("$selectedFiles", atCaret("explain [$selectedFiles"));
    }

    @Test
    void fileReferencesWithDirectoriesAreDetected() {
        assertEquals("@src/Main.java", atCaret("see @src/Main.java"));
        assertEquals("@src/Main.java", atCaret("@src/Main.java"));
        assertEquals("@Main.java", atCaret("foo/@Main.java"));
    }

    @Test
    void directivesAreDetected() {
        assertEquals("/skills", atCaret("/skills"));
        assertEquals("/prompts", atCaret("list /prompts"));
        assertEquals("/prompt:summary", atCaret("/prompt:summary"));
        assertEquals("/skill:optics", atCaret("! /skill:optics"));
    }

    @Test
    void noFragmentReturnsNull() {
        assertNull(atCaret(""));
        assertNull(atCaret("/"));
        assertNull(atCaret("$"));
        assertNull(atCaret("@"));
        assertNull(atCaret("seq without trigger"));
        assertNull(atCaret("abc$seq"));
        assertNull(atCaret("x@Main"));
        assertNull(atCaret("/unknown-command"));
    }

    @Test
    void onlyTheFragmentAtTheCaretCounts() {
        // a fragment earlier in the text does not matter when the caret is elsewhere
        assertEquals("$goals", atCaret("$seq and then $goals"));
        // inside a token the partial fragment is returned; it just resolves to nothing useful
        assertEquals("$s", AutocompleteInput.tokenFragmentAtCaret("$seq", 2));
    }
}
