// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.parser.proofjava;

import junit.framework.TestCase;
import recoder.ParserException;
import recoder.ServiceConfiguration;
import recoder.java.Expression;
import de.uka.ilkd.key.java.recoderext.KeYCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.java.recoderext.ProofJavaProgramFactory;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;

/**
 * 
 * TestCases for a modified ProofJavaParser which supports <...> for generics
 * and for implicit identifiers.
 * 
 * @author mulbrich
 * @version 2006-10-27
 */

public class TestProofJavaParser extends TestCase {

    static boolean debug = false;

    static ServiceConfiguration sc;

    static ProofJavaProgramFactory factory;

    protected void setUp() throws Exception {
        super.setUp();
        sc = new KeYCrossReferenceServiceConfiguration(
                new KeYRecoderExcHandler());
        factory = (ProofJavaProgramFactory) sc.getProgramFactory();
    }

    public void testGenericWithWithoutSpaces() throws ParserException {
        factory
                .parseCompilationUnit("class A < B > { B m() { return new B(); }}");
        factory
                .parseCompilationUnit("class A <B> { B m() { return new B(); }}");
    }

    private void testExpr(String expr) throws ParserException {
        try {
            Expression e = factory.parseExpression(expr);
            System.out.println(expr + " <-> " + e.toSource());
        } catch (ParserException ex) {
            throw new RuntimeException("Error with: " + expr, ex);
        }
    }

    public void testExpressions() throws ParserException {
        testExpr("<a>+2");
        testExpr("a >> <a>");
        testExpr("a<<b>-2");
        testExpr("A<T>.<B><S>.class");
    }

    public void testGenericClassDeclarations() throws ParserException {
        factory
                .parseCompilationUnit("class <A><B> { B m() { return new B(); }}");
        factory
                .parseCompilationUnit("class <A><E> { public <S><A>< <A><S> ><M>(){  } }");

    }

    public void testMemberDeclarations() throws ParserException {
        factory.parseMemberDeclaration("<A><T> <B> = <A>[].class;");
        factory.parseMemberDeclaration("private A<T>[];");
        factory.parseMemberDeclaration("private Type m() { };");
        factory.parseMemberDeclaration("private <Default> getDefault() { };");
        factory.parseMemberDeclaration("private <T> Type m() { };");
    }
        
}