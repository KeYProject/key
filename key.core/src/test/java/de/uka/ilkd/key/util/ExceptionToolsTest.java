/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.nio.file.Path;
import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.parsing.BuildingExceptions;
import de.uka.ilkd.key.util.parsing.BuildingIssue;

import org.key_project.util.helper.FindResources;
import org.key_project.util.parsing.Position;

import org.antlr.v4.runtime.CommonToken;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.Vocabulary;
import org.antlr.v4.runtime.VocabularyImpl;
import org.antlr.v4.runtime.misc.IntervalSet;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class ExceptionToolsTest {
    public static final Path testCaseDirectory =
        Objects.requireNonNull(FindResources.getTestCasesDirectory());

    /** Token type 1 displays as ';', token type 2 as 'int'. */
    private static final Vocabulary VOCAB =
        new VocabularyImpl(new String[] { null, "';'", "'int'" },
            new String[] { null, "SEMI", "INT" }, new String[] { null, "';'", "'int'" });

    @Test
    void describeSingleExpectedTokenNamesPunctuation() {
        Token found = new CommonToken(2, "}");
        String msg = ExceptionTools.describeSyntaxError(VOCAB, found, IntervalSet.of(1));
        assertEquals("';' (semicolon) expected, but found '}'", msg);
    }

    @Test
    void describeMultipleExpectedTokens() {
        Token found = new CommonToken(2, "}");
        String msg = ExceptionTools.describeSyntaxError(VOCAB, found, IntervalSet.of(1, 2));
        assertEquals("one of ';' (semicolon), 'int' expected, but found '}'", msg);
    }

    @Test
    void describeWithoutExpectedSetReportsUnexpectedToken() {
        Token found = new CommonToken(2, "}");
        assertEquals("unexpected '}'",
            ExceptionTools.describeSyntaxError(VOCAB, found, new IntervalSet()));
    }

    @Test
    void describeEofIsReadable() {
        Token eof = new CommonToken(Token.EOF, "<EOF>");
        String msg = ExceptionTools.describeSyntaxError(VOCAB, eof, IntervalSet.of(1));
        assertEquals("';' (semicolon) expected, but found end of file", msg);
    }

    @Test
    void getMessagesDigsIntoBundledIssuesAndSortsByPosition() {
        var late = new BuildingIssue("late problem", null, false, Position.newOneBased(5, 1),
            "file:///tmp/a.key");
        var early = new BuildingIssue("early problem", null, false, Position.newOneBased(2, 3),
            "file:///tmp/a.key");
        // wrap like the loader does, to make sure the wrapper does not hide the detail
        var wrapped = new RuntimeException("Failed to parse file",
            new BuildingExceptions(List.of(late, early)));

        List<PositionedString> messages = ExceptionTools.getMessages(wrapped);
        assertEquals(2, messages.size());
        // sorted by position: the line-2 issue comes first
        assertEquals("early problem", messages.get(0).getText());
        assertEquals(2, messages.get(0).getLocation().getPosition().line());
        assertEquals("late problem", messages.get(1).getText());
        assertEquals(5, messages.get(1).getLocation().getPosition().line());
    }

    @Test
    void getMessagesFallsBackToSingleMessage() {
        List<PositionedString> messages =
            ExceptionTools.getMessages(new RuntimeException("boom"));
        assertEquals(1, messages.size());
        assertEquals("boom", messages.get(0).getText());
    }

    @Test
    void getMessagesExpandsBundledProblemLoaderException() {
        // e.g. a partial proof replay where several rule applications could not be replayed: every
        // failure must be reported, not just the first.
        var sub1 = new ProblemLoaderException(null,
            "Error loading proof.\nLine 3, goal 5, rule andLeft not applicable");
        var sub2 = new ProblemLoaderException(null,
            "Error loading proof.\nLine 7, goal 9, rule impRight not applicable");
        var bundle = new ProblemLoaderException(null,
            "The proof could only be loaded partially: 2 rule application(s) could not be replayed.",
            List.of(sub1, sub2));

        List<PositionedString> messages = ExceptionTools.getMessages(bundle);
        // the summary plus one entry per failed rule application
        assertEquals(3, messages.size(), "expected summary + 2 failures, got: " + messages);
        assertTrue(messages.stream().anyMatch(m -> m.getText().contains("partially")),
            "summary should be present: " + messages);
        assertTrue(messages.stream().anyMatch(m -> m.getText().contains("andLeft")),
            "first failure should be present: " + messages);
        assertTrue(messages.stream().anyMatch(m -> m.getText().contains("impRight")),
            "second failure should be present (not dropped): " + messages);
    }
}
