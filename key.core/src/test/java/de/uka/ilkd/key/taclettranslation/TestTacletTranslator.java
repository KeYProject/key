/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.nparser.builder.ExpressionBuilder;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.rule.Taclet;

import org.antlr.v4.runtime.CharStreams;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

public class TestTacletTranslator {

    private NamespaceSet nss;
    private Services services;
    private KeyIO io;
    private Namespace<SchemaVariable> lastSchemaNamespace;


    // some methods essentially "stolen" from TestTacletParser

    private final static String DECLS = "\\sorts { S; }\n" + "\\functions {\n" + "  S const1;\n"
        + "  S const2;\n" + "}\n" + "\\schemaVariables {\n"
        + "  \\formula phi, psi, tau, assume_left, assume_right, add_left, add_right;\n"
        + "  \\term S x;\n" + "  \\variables S z;\n}\n";


    @BeforeEach
    public void setUp() throws Exception {
        nss = new NamespaceSet();
        services = new Services(AbstractProfile.getDefaultProfile());
        io = new KeyIO(services, nss);
    }

    private Term parseTerm(String s) {
        KeyAst.Term ctx = ParsingFacade.parseExpression(CharStreams.fromString(s));
        return (Term) ctx.accept(new ExpressionBuilder(services, nss, lastSchemaNamespace));
    }

    private Taclet parseTaclet(String s) {
        try {
            KeyIO.Loader load = io.load(s);
            List<Taclet> taclets =
                load.parseFile().loadDeclarations().loadSndDegreeDeclarations().loadTaclets();
            lastSchemaNamespace = load.getSchemaNamespace();
            return taclets.get(0);
        } catch (Exception e) {
            throw new RuntimeException("No Taclet in '" + s + "'", e);
        }
    }

    private void testTaclet(String tacletString, String termString) {
        tacletString = DECLS + "\n\\rules { " + tacletString + "; }";

        Taclet taclet = parseTaclet(tacletString);
        Term expected = parseTerm(termString);
        Term translation = SkeletonGenerator.DEFAULT_TACLET_TRANSLATOR.translate(taclet, services);

        Assertions.assertEquals(expected, translation,
            "Taclet " + taclet.name() + " not translated as expected");
    }

    //
    // The actual test cases go here
    //

    @Test
    public void testPropositional1() {
        testTaclet(
            "propositional1 { \n" + "\\assumes( assume_left ==> assume_right ) \n"
                + "\\find( const1 ) \n" + "\\replacewith( const2 ) \n"
                + "\\add( add_left ==> add_right ) \n" + "; \n" + "\\add( psi ==> ) }",

            // second case first. no replace means const1=const1

            "  ((const1 = const1 -> (!psi))" + " & (const1 = const2 -> (add_left -> add_right))) "
                + " -> (assume_left -> assume_right)");
    }

    @Test
    public void testPropositional2() {
        testTaclet(
            "propositionalLeft { \n" + "\\assumes( assume_left ==> assume_right ) \n"
                + "\\find( phi ==> ) \n" + "\\replacewith( psi ==> ) \n"
                + "\\add( add_left ==> add_right ) \n" + "; \n" + "\\add( tau ==> ) \n" + "; \n"
                + "\\replacewith( ==> psi )}",

            // last case first.

            "  (psi" + " & !tau " + " & (!psi | (add_left -> add_right))) "
                + " -> (!phi | (assume_left -> assume_right))");
    }

    @Test
    public void testNoPolarity() {
        testTaclet(
            "noPolarity { \n" + "\\assumes( assume_left ==> assume_right ) \n" + "\\find( phi  ) \n"
                + "\\replacewith( psi ); \n" + "\\replacewith( tau )}",

            // last case first.

            "  (!(phi <-> tau)" + " & !(phi <-> psi)) " + " -> (assume_left -> assume_right)");
    }

    @Test
    public void testPositivePolarity() {
        testTaclet(
            "positivePolarity { \n" + "\\assumes( assume_left ==> assume_right ) \n"
                + "\\find( phi  ) \n" + "\\succedentPolarity \n" + "\\replacewith( psi ); \n"
                + "\\replacewith( tau )}",

            // last case first.
            // for positive polarity w/o assumption,
            // this is equivalent to (tau -> phi) | (psi -> phi)

            "  (!(tau -> phi)" + " & !(psi -> phi)) " + " -> (assume_left -> assume_right)");
    }

    @Test
    public void testNegativePolarity() {
        testTaclet(
            "negativePolarity { \n" + "\\assumes( assume_left ==> assume_right ) \n"
                + "\\find( phi  ) \n" + "\\antecedentPolarity \n" + "\\replacewith( psi ); \n"
                + "\\replacewith( tau )}",

            // last case first.
            // for negative polarity w/o assumption,
            // this is equivalent to (tau <- phi) | (psi <- phi)

            "  (!(phi -> tau)" + " & !(phi -> psi)) " + " -> (assume_left -> assume_right)");
    }

    // TODO check refusal of varconds
    // TODO check skolem generation etc ...

}
