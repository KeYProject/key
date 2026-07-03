/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.util.collection.ImmutableArray;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;


public class LabeledTermImplTest {

    private TermServices services;
    private TermFactory tf;

    @BeforeEach
    public void setUp() {
        services = TacletForTests.services();
        tf = services.getTermFactory();

    }

    @Test
    public void testEqualsLabelOnTop() {
        JTerm unlabeledTerm =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.FALSE));

        ImmutableArray<TermLabel> labels =
            new ImmutableArray<>(ParameterlessTermLabel.ANON_HEAP_LABEL);

        JTerm labeledTerm = tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE),
            tf.createTerm(Junctor.FALSE), labels);

        // equals ignores term labels ...
        Assertions.assertEquals(labeledTerm, unlabeledTerm,
            "equals must ignore term labels");
        Assertions.assertEquals(unlabeledTerm, labeledTerm,
            "equals must ignore term labels");
        Assertions.assertEquals(labeledTerm.hashCode(), unlabeledTerm.hashCode(),
            "hashCode must ignore term labels");
        // ... while equalsIncludingLabels does not
        Assertions.assertFalse(labeledTerm.equalsIncludingLabels(unlabeledTerm),
            "equalsIncludingLabels must distinguish labeled and unlabeled terms");
        Assertions.assertFalse(unlabeledTerm.equalsIncludingLabels(labeledTerm),
            "equalsIncludingLabels must distinguish labeled and unlabeled terms");
        Assertions.assertTrue(labeledTerm.equalsIncludingLabels(labeledTerm));
    }

    /**
     * Labels on subterms must be distinguished by
     * {@link JTerm#equalsIncludingLabels(Object)}, too.
     */
    @Test
    public void testEqualsLabelOnSubterm() {
        JTerm labeledSub = tf.createTerm(Junctor.TRUE,
            new ImmutableArray<>(), null,
            new ImmutableArray<>(ParameterlessTermLabel.ANON_HEAP_LABEL));
        JTerm labeledBelow =
            tf.createTerm(Junctor.AND, labeledSub, tf.createTerm(Junctor.FALSE));
        JTerm unlabeled =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.FALSE));

        Assertions.assertTrue(labeledBelow.containsLabelsRecursive());
        Assertions.assertFalse(unlabeled.containsLabelsRecursive());
        Assertions.assertEquals(labeledBelow, unlabeled);
        Assertions.assertFalse(labeledBelow.equalsIncludingLabels(unlabeled));
        Assertions.assertFalse(unlabeled.equalsIncludingLabels(labeledBelow));
    }

    /**
     * A caching {@link TermFactory} must intern labeled terms label-sensitively: two
     * independently built, label-identical terms are the same object ({@code ==}), while a label
     * variant and the unlabeled term are kept distinct. This guards the {@code ==} fast paths and
     * memory sharing for the (very common) labeled terms.
     */
    @Test
    public void testCachedFactoryInternsLabeledTerms() {
        TermFactory ctf =
            new TermFactory(new java.util.HashMap<>());
        ImmutableArray<TermLabel> lbl =
            new ImmutableArray<>(ParameterlessTermLabel.ANON_HEAP_LABEL);

        JTerm labeled1 = ctf.createTerm(Junctor.AND,
            new ImmutableArray<>(ctf.createTerm(Junctor.TRUE), ctf.createTerm(Junctor.FALSE)),
            null, lbl);
        JTerm labeled2 = ctf.createTerm(Junctor.AND,
            new ImmutableArray<>(ctf.createTerm(Junctor.TRUE), ctf.createTerm(Junctor.FALSE)),
            null, lbl);
        JTerm unlabeled = ctf.createTerm(Junctor.AND,
            new ImmutableArray<>(ctf.createTerm(Junctor.TRUE), ctf.createTerm(Junctor.FALSE)),
            null, null);

        Assertions.assertSame(labeled1, labeled2, "identical labeled terms must be interned");
        Assertions.assertNotSame(labeled1, unlabeled,
            "labeled and unlabeled variants must not be interned together");
        Assertions.assertEquals(labeled1.labeledHashCode(), labeled2.labeledHashCode());
    }

    /**
     * Tests {@link JTerm#hasLabels()}, {@link JTerm#hasLabels()} and
     * {@link JTerm#containsLabel(TermLabel)}.
     */
    @Test
    public void testGetHasAndContainsLabels() {
        // Create terms
        JTerm unlabeled = services.getTermBuilder().tt();
        SymbolicExecutionTermLabel sedLabel = new SymbolicExecutionTermLabel(1);
        SymbolicExecutionTermLabel anotherSedLabel = new SymbolicExecutionTermLabel(2);
        JTerm oneLabel = services.getTermBuilder().label(unlabeled, sedLabel);
        JTerm oneLabelChanged =
            services.getTermBuilder().label(oneLabel, ParameterlessTermLabel.ANON_HEAP_LABEL);
        JTerm twoLabels = services.getTermBuilder().label(unlabeled,
            new ImmutableArray<>(ParameterlessTermLabel.ANON_HEAP_LABEL, sedLabel));
        JTerm oneLabelAdded0 =
            services.getTermBuilder().addLabel(oneLabel, ParameterlessTermLabel.ANON_HEAP_LABEL);
        JTerm oneLabelAdded1 = services.getTermBuilder().addLabel(oneLabelAdded0,
            ParameterlessTermLabel.ANON_HEAP_LABEL);
        // Test unlabeled
        Assertions.assertFalse(unlabeled.hasLabels());
        Assertions.assertNotNull(unlabeled.getLabels());
        Assertions.assertEquals(0, unlabeled.getLabels().size());
        Assertions.assertFalse(unlabeled.containsLabel(sedLabel));
        Assertions.assertFalse(unlabeled.containsLabel(ParameterlessTermLabel.ANON_HEAP_LABEL));
        Assertions.assertFalse(unlabeled.containsLabel(anotherSedLabel));
        // Test oneLabel
        Assertions.assertTrue(oneLabel.hasLabels());
        Assertions.assertNotNull(oneLabel.getLabels());
        Assertions.assertEquals(1, oneLabel.getLabels().size());
        Assertions.assertSame(sedLabel, oneLabel.getLabels().get(0));
        Assertions.assertTrue(oneLabel.containsLabel(sedLabel));
        Assertions.assertFalse(oneLabel.containsLabel(ParameterlessTermLabel.ANON_HEAP_LABEL));
        Assertions.assertFalse(oneLabel.containsLabel(anotherSedLabel));
        // Test oneLabeledAgain
        Assertions.assertTrue(oneLabelChanged.hasLabels());
        Assertions.assertNotNull(oneLabelChanged.getLabels());
        Assertions.assertEquals(1, oneLabelChanged.getLabels().size());
        Assertions.assertSame(ParameterlessTermLabel.ANON_HEAP_LABEL,
            oneLabelChanged.getLabels().get(0));
        Assertions.assertFalse(oneLabelChanged.containsLabel(sedLabel));
        Assertions
                .assertTrue(oneLabelChanged.containsLabel(ParameterlessTermLabel.ANON_HEAP_LABEL));
        Assertions.assertFalse(oneLabelChanged.containsLabel(anotherSedLabel));
        // Test twoLabels
        Assertions.assertTrue(twoLabels.hasLabels());
        Assertions.assertNotNull(twoLabels.getLabels());
        Assertions.assertEquals(2, oneLabelAdded0.getLabels().size());
        Assertions.assertEquals(2, oneLabelAdded1.getLabels().size());
        Assertions.assertEquals(2, twoLabels.getLabels().size());
        Assertions.assertSame(ParameterlessTermLabel.ANON_HEAP_LABEL, twoLabels.getLabels().get(0));
        Assertions.assertSame(sedLabel, twoLabels.getLabels().get(1));
        Assertions.assertTrue(twoLabels.containsLabel(sedLabel));
        Assertions.assertTrue(twoLabels.containsLabel(ParameterlessTermLabel.ANON_HEAP_LABEL));
        Assertions.assertFalse(twoLabels.containsLabel(anotherSedLabel));
    }
}
