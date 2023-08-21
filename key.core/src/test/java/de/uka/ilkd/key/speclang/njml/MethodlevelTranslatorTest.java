/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.io.IOException;
import java.io.InputStream;
import java.util.stream.Stream;

import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * @author Alexander Weigl
 * @version 1 (5/15/20)
 */
public class MethodlevelTranslatorTest {
    @TestFactory
    public Stream<DynamicTest> getFiles() throws IOException {
        InputStream resourceAsStream =
            ExpressionTranslatorTest.class.getResourceAsStream("methodlevel.txt");
        return ClasslevelTranslatorTest.readInputs(resourceAsStream, this::parseAndInterpret);
    }

    public void parseAndInterpret(String expr) {
        assertNotEquals("", expr);
        JmlLexer lexer = JmlFacade.createLexer(expr);
        JmlParser parser = new JmlParser(new CommonTokenStream(lexer));
        try {
            JmlParser.Methodlevel_commentContext ctx = parser.methodlevel_comment();
            if (parser.getNumberOfSyntaxErrors() != 0) {
                debugLexer(expr);
            }
        } catch (Exception e) {
            debugLexer(expr);
        }
        assertEquals(0, parser.getNumberOfSyntaxErrors());
    }

    private void debugLexer(String expr) {
        JmlLexer lexer = JmlFacade.createLexer(expr);
        DebugJmlLexer.debug(lexer);
    }
}
