/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;

import java.util.Arrays;
import java.util.Iterator;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class StringsTest {

    @Test
    void containsWholeWord() {
        String[] sentences = new String[] {
            "asfKeY;prover",
            "KeY prover",
            "KeY,prover",
            "KeY;prover",
            "key;prover"
        };
        assertTrue(Strings.containsWholeWord(sentences[0], "prover"));
        assertFalse(Strings.containsWholeWord(sentences[0], "KeY"));
        assertTrue(Strings.containsWholeWord(sentences[1], "prover"));
        assertTrue(Strings.containsWholeWord(sentences[1], "KeY"));
        assertTrue(Strings.containsWholeWord(sentences[2], "prover"));
        assertTrue(Strings.containsWholeWord(sentences[2], "KeY"));
        assertTrue(Strings.containsWholeWord(sentences[3], "prover"));
        assertTrue(Strings.containsWholeWord(sentences[3], "KeY"));
        assertTrue(Strings.containsWholeWord(sentences[4], "prover"));
        assertFalse(Strings.containsWholeWord(sentences[4], "KeY"));
    }

    @Test
    void isJMLComment() {
        String[] correctComments = {
            "/*@ requires ", "//@ requires",
            "/*+KeY@ requires", "//+KeY@ requires",
            "/*-OtherTool@", "//-OtherTool@"
        };
        String[] inCorrectComments = {
            "/* @ requires ", "// @ requires",
            "/*+OtherTool@ requires", "//+OtherTool@ requires",
            "/*-KeY@", "//*-KeY@"
        };

        for (var comment : correctComments) {
            assertTrue(Strings.isJMLComment(comment),
                "Classified correct comment as incorrect: " + comment);
        }
        for (var comment : inCorrectComments) {
            assertFalse(Strings.isJMLComment(comment),
                "Classified incorrect comment as correct: " + comment);
        }
    }

    @Test
    void formatAsList() {
        Iterator<String> it = Arrays.stream(new String[] { "a", "b", "c" }).iterator();
        assertEquals("%a;b;c$", Strings.formatAsList(it, '%', ';', '$'));

        it = Arrays.stream(new String[] { "a" }).iterator();
        assertEquals("%a$", Strings.formatAsList(it, '%', ';', '$'));

        it = Arrays.stream(new String[] {}).iterator();
        assertEquals("%$", Strings.formatAsList(it, '%', ';', '$'));
    }
}
