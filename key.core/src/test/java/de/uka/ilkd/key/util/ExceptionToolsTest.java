/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.io.IOException;
import java.net.MalformedURLException;
import java.nio.file.Path;
import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.util.parsing.BuildingExceptions;
import de.uka.ilkd.key.util.parsing.BuildingIssue;
import de.uka.ilkd.key.util.parsing.SyntaxErrorReporter;

import org.key_project.util.helper.FindResources;

import org.antlr.v4.runtime.CommonToken;
import org.antlr.v4.runtime.InputMismatchException;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.Vocabulary;
import org.antlr.v4.runtime.VocabularyImpl;
import org.antlr.v4.runtime.misc.IntervalSet;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class ExceptionToolsTest {
    public static final Path testCaseDirectory =
        Objects.requireNonNull(FindResources.getTestCasesDirectory());

    @Test
    void missingSemicolon() throws MalformedURLException {
        var fileToRead = testCaseDirectory;
        fileToRead = fileToRead.resolve("parserErrorTest/missing_semicolon.key");
        try {
            var result = ParsingFacade.parseFile(fileToRead);
            fail("should fail to parse");
        } catch (IOException e) {
            throw new RuntimeException(e);
        } catch (ParseCancellationException exc) {
            InputMismatchException ime = (InputMismatchException) exc.getCause();
            String message = """
                    Syntax error in input file missing_semicolon.key
                    Line: 6 Column: 1
                    ';' (semicolon) expected, but found '}'""";
            String resultMessage = ExceptionTools.getNiceMessage(ime);
            assertEquals(message, resultMessage);

            // The message describes the unexpected '}' (line 6), but the reported location points
            // just after the preceding construct (the taclet's closing brace '}' is on line 5 at
            // column 3, so the insertion point for the missing ';' is column 4).
            Location loc = ExceptionTools.getLocation(ime);
            assertEquals(5, loc.getPosition().line());
            assertEquals(4, loc.getPosition().column());
            assertEquals(fileToRead.toUri(), loc.fileUri());
        } catch (SyntaxErrorReporter.ParserException exception) {
            Location loc = ExceptionTools.getLocation(exception);
            assertEquals(5, loc.getPosition().line());
            assertEquals(4, loc.getPosition().column());
        }
    }

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
}
