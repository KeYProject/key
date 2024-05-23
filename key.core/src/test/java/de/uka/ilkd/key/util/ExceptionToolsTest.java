/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.io.File;
import java.io.IOException;
import java.net.MalformedURLException;

import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.parsing.SyntaxErrorReporter;

import org.key_project.util.helper.FindResources;

import org.antlr.v4.runtime.InputMismatchException;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class ExceptionToolsTest {
    public static final File testCaseDirectory = FindResources.getTestCasesDirectory();

    @Test
    void missingSemicolon() throws MalformedURLException {
        var fileToRead = testCaseDirectory.toPath();
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
                    Found token which was not expected: '}'
                    Expected token type(s): ';'
                    """;
            String resultMessage = ExceptionTools.getNiceMessage(ime);
            assertEquals(message, resultMessage);

            Location loc = ExceptionTools.getLocation(ime);
            assertEquals(6, loc.getPosition().line());
            assertEquals(1, loc.getPosition().column());
            assertEquals(fileToRead.toUri(), loc.fileUri());
        } catch (SyntaxErrorReporter.ParserException exception) {
            Location loc = ExceptionTools.getLocation(exception);
            assertEquals(6, loc.getPosition().line());
            assertEquals(1, loc.getPosition().column());
        }
    }
}
