/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder;

import java.nio.file.Path;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.JOperatorSV;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.HelperClassForTests;
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.key_project.logic.Name;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableSLList;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * class tests the building of Taclets in TacletBuilders, especially the checking if the
 * SchemaVariables fulfill certain conditions. They must not occur more than once in find and if
 * taken as a whole. Is obviously quite incomplete.
 */
public class TestTacletBuild {

    public static final JTerm[] NO_SUBTERMS = new JTerm[0];

    private TermFactory tf;

    private TermBuilder tb;

    @BeforeEach
    public void setUp() {
        TacletForTests.setStandardFile(TacletForTests.testRules);
        TacletForTests.parse();
        tb = TacletForTests.services().getTermBuilder();
        tf = tb.tf();
    }

    @Test
    public void test0() {
        SchemaVariable u = TacletForTests.getSchemaVariables().lookup("u");
        SchemaVariable v = TacletForTests.getSchemaVariables().lookup("v");
        JTerm b = tf.createTerm((JOperatorSV) TacletForTests.getSchemaVariables().lookup("b"),
            NO_SUBTERMS);
        JTerm t1 = tb.ex((QuantifiableVariable) u, b);
        JTerm t2 = tb.ex((QuantifiableVariable) v, b);
        RewriteTacletBuilder<RewriteTaclet> sb = new RewriteTacletBuilder<>();
        sb.setFind(t1);
        sb.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableSLList.nil(),
                t2));
        boolean thrown = false;
        try {
            sb.getTaclet();
        } catch (RuntimeException e) {
            thrown = true;
        }
        assertTrue(thrown, "An exception should be thrown as there are different "
            + "prefixes at different occurrences");
        sb.addVarsNotFreeIn(u, (SchemaVariable) b.op());
        sb.addVarsNotFreeIn(v, (SchemaVariable) b.op());
        sb.getTaclet(); // no exception is thrown here anymore
    }

    @Test
    public void testUniquenessOfIfAndFindVarSVsInIfAndFind() {
        boolean thrown = false;
        SchemaVariable u = TacletForTests.getSchemaVariables().lookup(new Name("u"));
        JTerm A = tf.createTerm(TacletForTests.getFunctions().lookup(new Name("A")),
            NO_SUBTERMS);
        JTerm t1 = tb.all((QuantifiableVariable) u, A);
        Sequent seq =
            JavaDLSequentKit.createSuccSequent(ImmutableSLList.singleton(new SequentFormula(t1)));
        JTerm t2 = tb.ex((QuantifiableVariable) u, A);
        SuccTacletBuilder sb = new SuccTacletBuilder();
        sb.setIfSequent(seq);
        sb.setFind(t2);
        try {
            sb.getTaclet();
        } catch (IllegalArgumentException e) {
            thrown = true;
        }
        assertTrue(thrown, "An exception should be thrown as a bound SchemaVariable "
            + "occurs more than once in the Taclets if and find");
    }

    @Test
    public void testUniquenessOfIfAndFindVarSVBothInIf() {
        boolean thrown = false;
        SchemaVariable u = TacletForTests.getSchemaVariables().lookup(new Name("u"));
        JTerm A = tf.createTerm(TacletForTests.getFunctions().lookup(new Name("A")),
            NO_SUBTERMS);
        JTerm t1 = tb.all((QuantifiableVariable) u, A);
        JTerm t2 = tb.ex((QuantifiableVariable) u, A);
        Sequent seq = JavaDLSequentKit
                .createSuccSequent(ImmutableSLList.singleton(new SequentFormula(t2))
                        .prepend(new SequentFormula(t1)));
        SuccTacletBuilder sb = new SuccTacletBuilder();
        sb.setIfSequent(seq);
        sb.setFind(A);
        try {
            sb.getTaclet();
        } catch (IllegalArgumentException e) {
            thrown = true;
        }
        assertTrue(thrown, "An exception should be thrown as a bound SchemaVariable "
            + "occurs more than once in the Taclets if and find");
    }

    @Test
    public void testUniquenessOfIfAndFindVarSVsInFind() {
        boolean thrown = false;
        SchemaVariable u = TacletForTests.getSchemaVariables().lookup(new Name("u"));
        JTerm A = tf.createTerm(TacletForTests.getFunctions().lookup(new Name("A")),
            NO_SUBTERMS);
        JTerm t1 = tb.all((QuantifiableVariable) u, A);
        SuccTacletBuilder sb = new SuccTacletBuilder();
        sb.setFind(tf.createTerm(Junctor.AND, t1, t1));
        try {
            sb.getTaclet();
        } catch (IllegalArgumentException e) {
            thrown = true;
        }
        assertTrue(thrown, "An exception should be thrown as a bound SchemaVariable "
            + "occurs more than once in the Taclets if and find");
    }

    private final HelperClassForTests helper = new HelperClassForTests();

    public static final Path testRules =
        HelperClassForTests.TESTCASE_DIRECTORY.resolve("tacletprefix");

    @Test
    public void testSchemavariablesInAddrulesRespectPrefix() {
        try {
            helper.parseThrowException(
                testRules.resolve("schemaVarInAddruleRespectPrefix.key"));
        } catch (BuildingException e) {
            assertTrue(e.toString().contains("schemaVarInAddruleRespectPrefix.key:9:3"),
                "Position of error message is wrong.");
            assertTrue(e.getCause().getMessage().contains(
                "Schema variable b (formula)occurs at different places in taclet all_left_hide with different prefixes."),
                "Cause should be prefix error");
            return;
        } catch (ProofInputException e) {
            fail("Unexpected exception");
        }
        fail("Expected an invalid prefix exception as the the addrule contains "
            + "a schemavariable with wrong prefix.");

    }
}
