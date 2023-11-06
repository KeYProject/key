/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.LinkedList;
import java.util.List;
import java.util.function.Consumer;
import java.util.stream.Stream;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;

import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (5/15/20)
 */
public class ClasslevelTranslatorTest {
    private static final Logger LOGGER = LoggerFactory.getLogger(ClasslevelTranslatorTest.class);

    @TestFactory
    Stream<DynamicTest> getFiles() throws IOException {
        InputStream resourceAsStream =
            ExpressionTranslatorTest.class.getResourceAsStream("classlevel.txt");
        return readInputs(resourceAsStream, this::parseAndInterpret);
    }

    static Stream<DynamicTest> readInputs(InputStream resourceAsStream, Consumer<String> fn)
            throws IOException {
        List<String> seq = new LinkedList<>();
        try (InputStream s = resourceAsStream;
                BufferedReader reader =
                    new BufferedReader(new InputStreamReader(s, StandardCharsets.UTF_8))) {
            String l;
            StringBuilder content = new StringBuilder();
            while ((l = reader.readLine()) != null) {
                if (l.trim().isEmpty() || l.startsWith("#")) {
                    continue;
                }
                content.append(l).append('\n');
            }
            final String[] split = content.toString().split("---\\s*Contract\\s*---\n");
            LOGGER.debug("cases: {}", split.length);
            for (String value : split) {
                value = value.trim();
                if (!value.isEmpty()) {
                    seq.add(value.replaceAll("---Contract---", ""));
                }
            }
        }
        return seq.stream().map(it -> DynamicTest.dynamicTest(it, () -> fn.accept(it)));
    }

    public void parseAndInterpret(String expr) {
        Assertions.assertNotEquals("", expr);
        KeYJavaType kjt = new KeYJavaType(Sort.ANY);
        ProgramVariable self = new LocationVariable(new ProgramElementName("self"), kjt);
        ProgramVariable result = new LocationVariable(new ProgramElementName("result"), kjt);
        ProgramVariable exc = new LocationVariable(new ProgramElementName("exc"), kjt);
        JmlLexer lexer = JmlFacade.createLexer(expr);
        JmlParser parser = new JmlParser(new CommonTokenStream(lexer));
        JmlParser.Classlevel_commentsContext ctx = parser.classlevel_comments();
        if (parser.getNumberOfSyntaxErrors() != 0) {
            System.out.println(expr);
            debugLexer(expr);
        }
        Assertions.assertEquals(0, parser.getNumberOfSyntaxErrors());
    }

    private void debugLexer(String expr) {
        JmlLexer lexer = JmlFacade.createLexer(expr);
        DebugJmlLexer.debug(lexer);
    }
}
