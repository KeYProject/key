/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;

import java.util.Arrays;
import java.util.List;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class StringsTest {

    @Test
    void containsWholeWord() {
        String[] sentences = {
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
            "/*-OtherTool@ requires", "//-OtherTool@ requires"
        };
        String[] inCorrectComments = {
            "/* @ requires ", "// @ requires",
            "/* +KeY@ requires", "//+KeY requires",
            "/*+OtherTool@ requires", "//+OtherTool@ requires",
            "/*-OtherTool requires", "//-OtherTool requires",
            "/*-KeY@ requires", "//*-KeY@ requires"
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
        List<String> testStrings = Arrays.asList("a", "b", "c");
        assertEquals("%a;b;c$", Strings.formatAsList(testStrings, "%", ";", "$"));

        assertEquals("%1;1;1$",
            Strings.formatAsList(testStrings, "%", ";", "$", String::length));

        testStrings = List.of("a");
        assertEquals("%a$", Strings.formatAsList(testStrings, "%", ";", "$"));

        testStrings = List.of();
        assertEquals("%$", Strings.formatAsList(testStrings, "%", ";", "$"));
    }
}
