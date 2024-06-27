/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

import java.util.Arrays;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.util.collection.ImmutableArray;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;
import static de.uka.ilkd.key.logic.equality.ProofIrrelevancyProperty.PROOF_IRRELEVANCY_PROPERTY;
import static de.uka.ilkd.key.logic.equality.RenamingSourceElementProperty.RENAMING_SOURCE_ELEMENT_PROPERTY;
import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;
import static de.uka.ilkd.key.logic.equality.TermLabelsProperty.TERM_LABELS_PROPERTY;
import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for {@link EqualsModProperty}.
 *
 * @author Tobias Reinhold
 */
public class TestEqualsModProperty {
    private TermBuilder tb;

    private TermFactory tf;

    final private TermLabel relevantLabel1 = ParameterlessTermLabel.UNDEFINED_VALUE_LABEL;
    final private TermLabel relevantLabel2 = ParameterlessTermLabel.SHORTCUT_EVALUATION_LABEL;
    private static TermLabel irrelevantLabel = null;
    final private static OriginTermLabelFactory factory = new OriginTermLabelFactory();

    @BeforeAll
    public static void setIrrelevantLabel() {
        try {
            irrelevantLabel = factory.parseInstance(Arrays.stream(new String[] {
                "User_Interaction @ node 0 (Test Test)", "[]" }).toList(),
                HelperClassForTests.createServices());
        } catch (TermLabelException e) {
            fail(e);
        }
    }

    @BeforeEach
    public void setUp() {
        tb = TacletForTests.services().getTermBuilder();
        tf = TacletForTests.services().getTermFactory();
    }

    // equalsModProperty(...) with RENAMING_TERM_PROPERTY
    @Test
    public void renaming() {
        // ------------ differing terms to begin with
        Term term1 =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.FALSE));
        Term term2 =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.TRUE));
        assertFalse(term1.equalsModProperty(term2, RENAMING_TERM_PROPERTY),
            "Terms are different to begin with, so they shouldn't be equal");
        assertFalse(term2.equalsModProperty(term1, RENAMING_TERM_PROPERTY),
            "Terms are different to begin with, so they shouldn't be equal");
        // other tests for equality already in TestTerm.java

        // ------------ comparison with something that is not a term
        assertFalse(term1.equalsModProperty(1, RENAMING_TERM_PROPERTY),
            "Should be false as other object is not a term");

        // ------------ differing labels
        term1 =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.FALSE));
        term2 =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.FALSE));
        ImmutableArray<TermLabel> labels1 = new ImmutableArray<>(irrelevantLabel);
        term1 = tb.label(term1, labels1);
        assertTrue(term1.equalsModProperty(term2, RENAMING_TERM_PROPERTY),
            "Should be true as labels do not matter");
        assertTrue(term2.equalsModProperty(term1, RENAMING_TERM_PROPERTY),
            "Should be true as labels do not matter");

        labels1 = new ImmutableArray<>(relevantLabel1);
        term1 = tb.label(term1, labels1);
        assertTrue(term1.equalsModProperty(term2, RENAMING_TERM_PROPERTY),
            "Should be true as labels do not matter");
        assertTrue(term2.equalsModProperty(term1, RENAMING_TERM_PROPERTY),
            "Should be true as labels do not matter");

        ImmutableArray<TermLabel> labels2 = new ImmutableArray<>(relevantLabel2);
        term2 = tb.label(term2, labels2);
        assertTrue(term1.equalsModProperty(term2, RENAMING_TERM_PROPERTY),
            "Should be true as labels do not matter");
        assertTrue(term2.equalsModProperty(term1, RENAMING_TERM_PROPERTY),
            "Should be true as labels do not matter");
    }

    // equalsModProperty(...) with IRRELEVANT_TERM_LABELS_PROPERTY
    @Test
    public void irrelevantTermLabels() {
        // ------------ different terms to begin with
        Term term1 =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.FALSE));
        Term term2 =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.TRUE));
        assertFalse(term1.equalsModProperty(term2, IRRELEVANT_TERM_LABELS_PROPERTY),
            "Terms are different to begin with, so they shouldn't be equal");
        assertFalse(term2.equalsModProperty(term1, IRRELEVANT_TERM_LABELS_PROPERTY),
            "Terms are different to begin with, so they shouldn't be equal");

        // ------------ comparison with something that is not a term
        assertFalse(term1.equalsModProperty(1, IRRELEVANT_TERM_LABELS_PROPERTY),
            "Should be false as other object is not a term");

        // base terms stay the same for the rest of the tests
        term1 =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.FALSE));
        term2 =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.FALSE));

        // ------------ only one term has labels
        ImmutableArray<TermLabel> labels1 =
            new ImmutableArray<>(relevantLabel1, irrelevantLabel);
        term1 = tb.label(term1, labels1);
        assertFalse(term1.equalsModProperty(term2, IRRELEVANT_TERM_LABELS_PROPERTY),
            "Should be false as term1 has a proof relevant term label, but term2 does not have any labels");
        assertFalse(term2.equalsModProperty(term1, IRRELEVANT_TERM_LABELS_PROPERTY),
            "Should be false as term1 has a proof relevant term label, but term2 does not have any labels");

        labels1 = new ImmutableArray<>(irrelevantLabel);
        term1 = tb.label(term1, labels1);
        assertTrue(term1.equalsModProperty(term2, IRRELEVANT_TERM_LABELS_PROPERTY),
            "Should be true as term1 has no relevant term labels and term2 does not have any labels");
        assertTrue(term2.equalsModProperty(term1, IRRELEVANT_TERM_LABELS_PROPERTY),
            "Should be true as term1 has no relevant term labels and term2 does not have any labels");

        // ------------ same relevant labels
        labels1 = new ImmutableArray<>(relevantLabel1, relevantLabel2);
        ImmutableArray<TermLabel> labels2 =
            new ImmutableArray<>(relevantLabel1, relevantLabel2, irrelevantLabel);
        term1 = tb.label(term1, labels1);
        term2 = tb.label(term2, labels2);
        assertTrue(term1.equalsModProperty(term2, IRRELEVANT_TERM_LABELS_PROPERTY),
            "Should be true as both terms have the same relevant term labels");
        assertTrue(term2.equalsModProperty(term1, IRRELEVANT_TERM_LABELS_PROPERTY),
            "Should be true as both terms have the same relevant term labels");

        // ------------ not the same relevant labels
        labels1 = new ImmutableArray<>(relevantLabel1, irrelevantLabel);
        labels2 = new ImmutableArray<>(relevantLabel1, relevantLabel2);
        term1 = tb.label(term1, labels1);
        term2 = tb.label(term2, labels2);
        assertFalse(term1.equalsModProperty(term2, IRRELEVANT_TERM_LABELS_PROPERTY),
            "Should be false as terms do not have the same relevant term labels");
        assertFalse(term2.equalsModProperty(term1, IRRELEVANT_TERM_LABELS_PROPERTY),
            "Should be false as terms do not have the same relevant term labels");
    }

    // equalsModProperty(...) with TERM_LABELS_PROPERTY
    @Test
    public void allTermLabels() {
        // ------------ different terms to begin with
        Term term1 =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.FALSE));
        Term term2 =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.TRUE));
        assertFalse(term1.equalsModProperty(term2, TERM_LABELS_PROPERTY),
            "Terms are different to begin with, so they shouldn't be equal");
        assertFalse(term2.equalsModProperty(term1, TERM_LABELS_PROPERTY),
            "Terms are different to begin with, so they shouldn't be equal");

        // ------------ comparison with something that is not a term
        assertFalse(term1.equalsModProperty(1, TERM_LABELS_PROPERTY),
            "Should be false as other object is not a term");

        // base terms stay the same for the rest of the tests
        term1 =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.FALSE));
        term2 =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.FALSE));

        // ------------ only one term has labels
        ImmutableArray<TermLabel> labels1 =
            new ImmutableArray<>(relevantLabel1, irrelevantLabel);
        term1 = tb.label(term1, labels1);
        assertTrue(term1.equalsModProperty(term2, TERM_LABELS_PROPERTY),
            "Should be true as underlying terms are equal");
        assertTrue(term2.equalsModProperty(term1, TERM_LABELS_PROPERTY),
            "Should be true as underlying terms are equal");

        // ------------ same relevant labels
        labels1 = new ImmutableArray<>(relevantLabel1, relevantLabel2);
        ImmutableArray<TermLabel> labels2 =
            new ImmutableArray<>(relevantLabel1, relevantLabel2, irrelevantLabel);
        term1 = tb.label(term1, labels1);
        term2 = tb.label(term2, labels2);
        assertTrue(term1.equalsModProperty(term2, TERM_LABELS_PROPERTY),
            "Should be true as underlying terms are equal");
        assertTrue(term2.equalsModProperty(term1, TERM_LABELS_PROPERTY),
            "Should be true as underlying terms are equal");

        // ------------ not the same relevant labels
        labels1 = new ImmutableArray<>(relevantLabel1, irrelevantLabel);
        labels2 = new ImmutableArray<>(relevantLabel1, relevantLabel2);
        term1 = tb.label(term1, labels1);
        term2 = tb.label(term2, labels2);
        assertTrue(term1.equalsModProperty(term2, TERM_LABELS_PROPERTY),
            "Should be true as underlying terms are equal");
        assertTrue(term2.equalsModProperty(term1, TERM_LABELS_PROPERTY),
            "Should be true as underlying terms are equal");
    }

    // equalsModProperty(...) with PROOF_IRRELEVANCY_PROPERTY
    @Test
    public void proofIrrelevancy() {
        // ------------ different terms to begin with
        Term term1 =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.FALSE));
        Term term2 =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.TRUE));
        assertFalse(term1.equalsModProperty(term2, PROOF_IRRELEVANCY_PROPERTY),
            "Terms are different to begin with, so they shouldn't be equal");
        assertFalse(term2.equalsModProperty(term1, PROOF_IRRELEVANCY_PROPERTY),
            "Terms are different to begin with, so they shouldn't be equal");

        // ------------ comparison with something that is not a term
        assertFalse(term1.equalsModProperty(1, PROOF_IRRELEVANCY_PROPERTY),
            "Should be false as other object is not a term");

        // base terms stay the same for the rest of the tests
        term1 =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.FALSE));
        term2 =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.FALSE));

        // ------------ only one term has labels
        ImmutableArray<TermLabel> labels1 =
            new ImmutableArray<>(relevantLabel1, irrelevantLabel);
        term1 = tb.label(term1, labels1);
        assertFalse(term1.equalsModProperty(term2, PROOF_IRRELEVANCY_PROPERTY),
            "Should be false as term1 has a proof relevant term label, but term2 does not have any labels");
        assertFalse(term2.equalsModProperty(term1, PROOF_IRRELEVANCY_PROPERTY),
            "Should be false as term1 has a proof relevant term label, but term2 does not have any labels");

        labels1 = new ImmutableArray<>(irrelevantLabel);
        term1 = tb.label(term1, labels1);
        assertTrue(term1.equalsModProperty(term2, PROOF_IRRELEVANCY_PROPERTY),
            "Should be true as term1 has no relevant term labels and term2 does not have any labels");
        assertTrue(term2.equalsModProperty(term1, PROOF_IRRELEVANCY_PROPERTY),
            "Should be true as term1 has no relevant term labels and term2 does not have any labels");

        // ------------ same relevant labels
        labels1 = new ImmutableArray<>(relevantLabel1, relevantLabel2, irrelevantLabel);
        ImmutableArray<TermLabel> labels2 =
            new ImmutableArray<>(relevantLabel1, relevantLabel2, irrelevantLabel);
        term1 = tb.label(term1, labels1);
        term2 = tb.label(term2, labels2);
        assertTrue(term1.equalsModProperty(term2, PROOF_IRRELEVANCY_PROPERTY),
            "Should be true as both terms have the same relevant term labels");
        assertTrue(term2.equalsModProperty(term1, PROOF_IRRELEVANCY_PROPERTY),
            "Should be true as both terms have the same relevant term labels");

        labels1 = new ImmutableArray<>(relevantLabel1, relevantLabel2, irrelevantLabel);
        labels2 = new ImmutableArray<>(relevantLabel1, relevantLabel2);
        term1 = tb.label(term1, labels1);
        term2 = tb.label(term2, labels2);
        assertTrue(term1.equalsModProperty(term2, PROOF_IRRELEVANCY_PROPERTY),
            "Should be true as both terms have the same relevant term labels and irrelevant labels do not matter");
        assertTrue(term2.equalsModProperty(term1, PROOF_IRRELEVANCY_PROPERTY),
            "Should be true as both terms have the same relevant term labels and irrelevant labels do not matter");

        // ------------ not the same relevant labels
        labels1 = new ImmutableArray<>(relevantLabel1);
        labels2 = new ImmutableArray<>(relevantLabel2);
        term1 = tb.label(term1, labels1);
        term2 = tb.label(term2, labels2);
        assertFalse(term1.equalsModProperty(term2, PROOF_IRRELEVANCY_PROPERTY),
            "Should be false as terms do not have the same relevant term labels");
        assertFalse(term2.equalsModProperty(term1, PROOF_IRRELEVANCY_PROPERTY),
            "Should be false as terms do not have the same relevant term labels");
    }

    @Test
    public void renamingSourceElements() {
        Term match1 = TacletForTests.parseTerm("\\<{ int i; int j; /*Test*/ }\\>true");
        Term match2 = TacletForTests.parseTerm("\\<{ int i; /*Another test*/ int k; }\\>true");
        assertTrue(
            match1.equalsModProperty(match2, RenamingTermProperty.RENAMING_TERM_PROPERTY),
            "Terms should be equalModRenaming (0).");

        Comment testComment = new Comment("test");
        StringLiteral stringLiteral = new StringLiteral("testStringLiteral");

        assertFalse(testComment.equalsModProperty(stringLiteral, RENAMING_SOURCE_ELEMENT_PROPERTY,
            new NameAbstractionTable()));
        assertFalse(stringLiteral.equalsModProperty(testComment, RENAMING_SOURCE_ELEMENT_PROPERTY,
            new NameAbstractionTable()));
    }
}
