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

package de.uka.ilkd.key.taclettranslation;

import java.io.PrintWriter;
import java.io.StringWriter;

import junit.framework.TestCase;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.rule.Taclet;

public class TestTacletTranslator extends TestCase {

    private NamespaceSet nss;
    private Services services;


    public TestTacletTranslator(String name) {
        super(name);
    }

    // some methods essentially "stolen" from TestTacletParser

    protected void setUp() throws Exception {
        nss = new NamespaceSet();
        services = new Services(AbstractProfile.getDefaultProfile());

        parseDecls("\\sorts { S; }\n" +
                "\\functions {\n" +
                "  S const1;\n" +
                "  S const2;\n" +
                "}\n" +
                "\\schemaVariables {\n" +
                "  \\formula phi, psi, tau, assume_left, assume_right, add_left, add_right;\n" +
                "  \\term S x;\n" +
                "  \\variables S z;\n" +
                "}\n");
    }

    //
    // Utility Methods for test cases.
    //
    private KeYParserF stringTacletParser(String s) {
	return new KeYParserF(ParserMode.TACLET,
		new KeYLexerF(s,
			"No file. parser/TestTacletParser.stringTacletParser(" + s + ")"),
		services, nss);
    }

    private void parseDecls(String s) {
        try {
	    KeYParserF p = new KeYParserF(ParserMode.DECLARATION,
		    new KeYLexerF(s,
			    "No file. parser/TestTacletParser.stringDeclParser(" + s + ")"),
		   services, nss);
            p.decls();
        } catch (Exception e) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            e.printStackTrace(pw);
            throw new RuntimeException("Exc while Parsing:\n" + sw);
        }
    }

    private Term parseTerm(String s) {
        try {
            KeYParserF p = stringTacletParser(s);
            return p.term();
        } catch (Exception e) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            e.printStackTrace(pw);
            throw new RuntimeException("Exc while Parsing:\n" + sw);
        }
    }

    private Term parseFma(String s) {
        try {
            KeYParserF p = stringTacletParser(s);

            return p.formula();
        } catch (Exception e) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            e.printStackTrace(pw);
            throw new RuntimeException("Exc while Parsing:\n" + sw);
        }
    }

    private Taclet parseTaclet(String s) {
        try {
            KeYParserF p = stringTacletParser(s);

            return p.taclet(DefaultImmutableSet.<Choice> nil());
        } catch (Exception e) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            e.printStackTrace(pw);
            throw new RuntimeException("Exc while Parsing:\n" + sw);
        }
    }

    private void testTaclet(String tacletString, String termString) throws Exception {

        Taclet taclet = parseTaclet(tacletString);
        Term expected = parseTerm(termString);
        Term translation = SkeletonGenerator.DEFAULT_TACLET_TRANSLATOR.translate(taclet, services);

        assertEquals("Taclet " + taclet.name() + " not translated as expected", expected,
                translation);
    }

    //
    // The actual test cases go here
    //

    public void testPropositional1() throws Exception {
        testTaclet("propositional1 { \n" +
                "\\assumes( assume_left ==> assume_right ) \n" +
                "\\find( const1 ) \n" +
                "\\replacewith( const2 ) \n" +
                "\\add( add_left ==> add_right ) \n" +
                "; \n" +
                "\\add( psi ==> ) }",

                // second case first. no replace means const1=const1

                "  ((const1 = const1 -> (!psi))" +
                " & (const1 = const2 -> (add_left -> add_right))) " +
                " -> (assume_left -> assume_right)");
    }

    public void testPropositional2() throws Exception {
        testTaclet("propositionalLeft { \n" +
                "\\assumes( assume_left ==> assume_right ) \n" +
                "\\find( phi ==> ) \n" +
                "\\replacewith( psi ==> ) \n" +
                "\\add( add_left ==> add_right ) \n" +
                "; \n" +
                "\\add( tau ==> ) \n" +
                "; \n" +
                "\\replacewith( ==> psi )}", 

                // last case first. 

                "  (psi" +
                " & !tau " +
                " & (!psi | (add_left -> add_right))) " +
                " -> (!phi | (assume_left -> assume_right))");
    }
    
    public void testNoPolarity() throws Exception {
        testTaclet("noPolarity { \n" +
                "\\assumes( assume_left ==> assume_right ) \n" +
                "\\find( phi  ) \n" +
                "\\replacewith( psi ); \n" +
                "\\replacewith( tau )}", 

                // last case first. 

                "  (!(phi <-> tau)" +
                " & !(phi <-> psi)) " +
                " -> (assume_left -> assume_right)");
    }
    
    public void testPositivePolarity() throws Exception {
        testTaclet("positivePolarity { \n" +
                "\\assumes( assume_left ==> assume_right ) \n" +
                "\\find( phi  ) \n" +
                "\\succedentPolarity \n" +
                "\\replacewith( psi ); \n" +
                "\\replacewith( tau )}", 

                // last case first.
                // for positive polarity w/o assumption,
                // this is equivalent to (tau -> phi) | (psi -> phi)

                "  (!(tau -> phi)" +
                " & !(psi -> phi)) " +
                " -> (assume_left -> assume_right)");
    }
    
    public void testNegativePolarity() throws Exception {
        testTaclet("negativePolarity { \n" +
                "\\assumes( assume_left ==> assume_right ) \n" +
                "\\find( phi  ) \n" +
                "\\antecedentPolarity \n" +
                "\\replacewith( psi ); \n" +
                "\\replacewith( tau )}", 

                // last case first.
                // for negative polarity w/o assumption,
                // this is equivalent to (tau <- phi) | (psi <- phi)

                "  (!(phi -> tau)" +
                " & !(phi -> psi)) " +
                " -> (assume_left -> assume_right)");
    }

    // TODO check refusal of varconds
    // TODO check skolem generation etc ...
    
}