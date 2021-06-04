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

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.nparser.builder.BuildingException;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.SuccTacletBuilder;
import de.uka.ilkd.key.util.HelperClassForTests;
import org.junit.Before;
import org.junit.Test;
import org.key_project.util.collection.ImmutableSLList;

import java.io.File;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

/**
 * class tests the building of Taclets in TacletBuilders, especially the
 * checking if the SchemaVariables fulfill certain conditions. They must
 * not occur more than once in find and if taken as a whole. Is obviously
 * quite incomplete.
 */

public class TestTacletBuild {
    public static final Term[] NO_SUBTERMS = new Term[0];

    private TermFactory tf;

    private TermBuilder tb;

    @Before
    public void setUp() {
        TacletForTests.setStandardFile(TacletForTests.testRules);
        TacletForTests.parse();
        tb = TacletForTests.services().getTermBuilder();
        tf = tb.tf();
    }

    @Test
    public void test0() {
        SchemaVariable u =
                TacletForTests.getSchemaVariables().lookup(new Name("u"));
        SchemaVariable v =
                TacletForTests.getSchemaVariables().lookup(new Name("v"));
        Term b = tf.createTerm(
                TacletForTests.getSchemaVariables().lookup(new Name("b")), NO_SUBTERMS);
        Term t1 = tb.ex((QuantifiableVariable) u, b);
        Term t2 = tb.ex((QuantifiableVariable) v, b);
        RewriteTacletBuilder<RewriteTaclet> sb = new RewriteTacletBuilder<>();
        sb.setFind(t1);
        sb.addTacletGoalTemplate
                (new RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
                        ImmutableSLList.nil(),
                        t2));
        boolean thrown = false;
        try {
            sb.getTaclet();
        } catch (RuntimeException e) {
            thrown = true;
        }
        assertTrue("An exception should be thrown as there are different "
                + "prefixes at different occurrences", thrown);
        sb.addVarsNotFreeIn(u, (SchemaVariable) b.op());
        sb.addVarsNotFreeIn(v, (SchemaVariable) b.op());
        sb.getTaclet();  //no exception is thrown here anymore

    }

    @Test
    public void testUniquenessOfIfAndFindVarSVsInIfAndFind() {
        boolean thrown = false;
        SchemaVariable u =
                TacletForTests.getSchemaVariables().lookup(new Name("u"));
        Term A = tf.createTerm(TacletForTests.getFunctions().lookup(new Name("A")),
                NO_SUBTERMS);
        Term t1 = tb.all((QuantifiableVariable) u, A);
        Sequent seq = Sequent.createSuccSequent
                (Semisequent.EMPTY_SEMISEQUENT.insert
                        (0, new SequentFormula(t1)).semisequent());
        Term t2 = tb.ex((QuantifiableVariable) u, A);
        SuccTacletBuilder sb = new SuccTacletBuilder();
        sb.setIfSequent(seq);
        sb.setFind(t2);
        try {
            sb.getTaclet();
        } catch (IllegalArgumentException e) {
            thrown = true;
        }
        assertTrue("An exception should be thrown as a bound SchemaVariable " +
                "occurs more than once in the Taclets if and find", thrown);
    }


    @Test
    public void testUniquenessOfIfAndFindVarSVBothInIf() {
        boolean thrown = false;
        SchemaVariable u =
                TacletForTests.getSchemaVariables().lookup(new Name("u"));
        Term A = tf.createTerm
                (TacletForTests.getFunctions().lookup(new Name("A")),
                        NO_SUBTERMS);
        Term t1 = tb.all((QuantifiableVariable) u, A);
        Term t2 = tb.ex((QuantifiableVariable) u, A);
        Sequent seq = Sequent.createSuccSequent
                (Semisequent.EMPTY_SEMISEQUENT
                        .insert(0, new SequentFormula(t1)).semisequent()
                        .insert(1, new SequentFormula(t2)).semisequent());
        SuccTacletBuilder sb = new SuccTacletBuilder();
        sb.setIfSequent(seq);
        sb.setFind(A);
        try {
            sb.getTaclet();
        } catch (IllegalArgumentException e) {
            thrown = true;
        }
        assertTrue("An exception should be thrown as a bound SchemaVariable "
                + "occurs more than once in the Taclets if and find", thrown);
    }

    @Test
    public void testUniquenessOfIfAndFindVarSVsInFind() {
        boolean thrown = false;
        SchemaVariable u =
                TacletForTests.getSchemaVariables().lookup(new Name("u"));
        Term A = tf.createTerm
                (TacletForTests.getFunctions().lookup(new Name("A")),
                        NO_SUBTERMS);
        Term t1 = tb.all((QuantifiableVariable) u, A);
        SuccTacletBuilder sb = new SuccTacletBuilder();
        sb.setFind(tf.createTerm(Junctor.AND, t1, t1));
        try {
            sb.getTaclet();
        } catch (IllegalArgumentException e) {
            thrown = true;
        }
        assertTrue("An exception should be thrown as a bound SchemaVariable " +
                "occurs more than once in the Taclets if and find", thrown);
    }

    private final HelperClassForTests helper = new HelperClassForTests();

    public static final String testRules = HelperClassForTests.TESTCASE_DIRECTORY + File.separator + "tacletprefix";

    @Test
    public void testSchemavariablesInAddrulesRespectPrefix() {
        try {
            helper.parseThrowException(new File(testRules + File.separator +
                    "schemaVarInAddruleRespectPrefix.key"));
        } catch (BuildingException e) {
            assertTrue("Position of error message is wrong.",
                    e.getMessage().contains("schemaVarInAddruleRespectPrefix.key:21:2"));
            assertTrue("Cause should be prefix error",
                    e.getCause().getMessage()
                            .contains("Schema variable b (formula)occurs at different places in taclet all_left_hide with different prefixes."));
            return;
        } catch (ProofInputException e) {
            fail("Unexpected exception");
        }
        fail("Expected an invalid prefix exception as the the addrule contains " +
                "a schemavariable with wrong prefix.");

    }
}