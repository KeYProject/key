/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser.proofjava;

import de.uka.ilkd.key.java.recoderext.KeYCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.java.recoderext.ProofJavaProgramFactory;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.ParserException;
import recoder.ServiceConfiguration;
import recoder.java.Expression;

/**
 *
 * TestCases for a modified ProofJavaParser which supports <...> for generics and for implicit
 * identifiers.
 *
 * @author mulbrich
 * @version 2006-10-27
 */

public class TestProofJavaParser {
    private static final Logger LOGGER = LoggerFactory.getLogger(TestProofJavaParser.class);

    private static ServiceConfiguration sc;

    private static ProofJavaProgramFactory factory;

    @BeforeEach
    public void setUp() throws Exception {
        sc = new KeYCrossReferenceServiceConfiguration(new KeYRecoderExcHandler());
        factory = (ProofJavaProgramFactory) sc.getProgramFactory();
    }

    @Test
    public void testGenericWithWithoutSpaces() throws ParserException {
        factory.parseCompilationUnit("class A < B > { B m() { return new B(); }}");
        factory.parseCompilationUnit("class A <B> { B m() { return new B(); }}");
    }

    private void testExpr(String expr) {
        try {
            Expression e = factory.parseExpression(expr);
            LOGGER.debug(expr + " <-> " + e.toSource());
        } catch (ParserException ex) {
            throw new RuntimeException("Error with: " + expr, ex);
        }
    }

    @Test
    public void testExpressions() {
        testExpr("<a>+2");
        testExpr("a >> <a>");
        testExpr("a<<b>-2");
        testExpr("A<T>.<B><S>.class");
    }

    @Test
    public void testGenericClassDeclarations() throws ParserException {
        factory.parseCompilationUnit("class <A><B> { B m() { return new B(); }}");
        factory.parseCompilationUnit("class <A><E> { public <S><A>< <A><S> ><M>(){  } }");

    }

    @Test
    public void testMemberDeclarations() throws ParserException {
        factory.parseMemberDeclaration("<A><T> <B> = <A>[].class;");
        factory.parseMemberDeclaration("private A<T>[];");
        factory.parseMemberDeclaration("private Type m() { };");
        factory.parseMemberDeclaration("private <Default> getDefault() { };");
        factory.parseMemberDeclaration("private <T> Type m() { };");
    }

}
