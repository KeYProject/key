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

import static org.junit.jupiter.api.Assertions.assertNotEquals;

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
        Term unlabeledTerm =
            tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE), tf.createTerm(Junctor.FALSE));

        ImmutableArray<TermLabel> labels =
            new ImmutableArray<>(ParameterlessTermLabel.ANON_HEAP_LABEL);

        Term labeledTerm = tf.createTerm(Junctor.AND, tf.createTerm(Junctor.TRUE),
            tf.createTerm(Junctor.FALSE), labels);

        assertNotEquals(labeledTerm, unlabeledTerm,
            "Labeled and unlabeled terms must not be equal");
        assertNotEquals(unlabeledTerm, labeledTerm,
            "Labeled and unlabeled terms must not be equal");
    }

    /**
     * Tests {@link Term#hasLabels()}, {@link Term#hasLabels()} and
     * {@link Term#containsLabel(TermLabel)}.
     */
    @Test
    public void testGetHasAndContainsLabels() {
        // Create terms
        Term unlabeled = services.getTermBuilder().tt();
        SymbolicExecutionTermLabel sedLabel = new SymbolicExecutionTermLabel(1);
        SymbolicExecutionTermLabel anotherSedLabel = new SymbolicExecutionTermLabel(2);
        Term oneLabel = services.getTermBuilder().label(unlabeled, sedLabel);
        Term oneLabelChanged =
            services.getTermBuilder().label(oneLabel, ParameterlessTermLabel.ANON_HEAP_LABEL);
        Term twoLabels = services.getTermBuilder().label(unlabeled,
            new ImmutableArray<>(ParameterlessTermLabel.ANON_HEAP_LABEL, sedLabel));
        Term oneLabelAdded0 =
            services.getTermBuilder().addLabel(oneLabel, ParameterlessTermLabel.ANON_HEAP_LABEL);
        Term oneLabelAdded1 = services.getTermBuilder().addLabel(oneLabelAdded0,
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
