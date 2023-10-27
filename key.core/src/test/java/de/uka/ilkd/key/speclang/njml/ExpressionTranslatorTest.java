/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.njml;

import java.util.HashMap;

import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.util.collection.ImmutableSLList;

import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvFileSource;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (5/14/20)
 */
public class ExpressionTranslatorTest {
    private static final Logger LOGGER = LoggerFactory.getLogger(ExpressionTranslatorTest.class);

    private Services services;

    @BeforeEach
    public void setup() {
        if (services != null) {
            return;
        }
        services = TacletForTests.services();
        Recoder2KeY r2k = new Recoder2KeY(services, services.getNamespaces());
        r2k.parseSpecialClasses();
    }

    @ParameterizedTest
    @CsvFileSource(resources = "exprs.txt", delimiter = '^')
    public void parseAndInterpret(String expr) {
        KeYJavaType kjt = new KeYJavaType(Sort.ANY);
        LocationVariable self = new LocationVariable(new ProgramElementName("self"), kjt);
        LocationVariable result = new LocationVariable(new ProgramElementName("result"), kjt);
        LocationVariable exc = new LocationVariable(new ProgramElementName("exc"), kjt);
        JmlLexer lexer = JmlFacade.createLexer(expr);
        lexer._mode = JmlLexer.expr;
        JmlParser parser = new JmlParser(new CommonTokenStream(lexer));
        JmlParser.ExpressionContext ctx = parser.expression();
        Assertions.assertEquals(0, parser.getNumberOfSyntaxErrors());
        Translator et = new Translator(services, kjt, self, SpecMathMode.defaultMode(),
            ImmutableSLList.nil(), result, exc, new HashMap<>(), new HashMap<>());
        LOGGER.debug("{}", ctx.accept(et));
    }
}
