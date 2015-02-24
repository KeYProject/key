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

package de.uka.ilkd.key.logic;

import junit.framework.TestCase;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.rule.TacletForTests;

public class LabeledTermImplTest extends TestCase {

        private TermServices services;
        private TermFactory tf;

        @Override
        public void setUp() {
            services = TacletForTests.services();
            tf = services.getTermFactory();

        }
    
	public void testEqualsLabelOnTop() {
                Term unlabeledTerm = 
				tf.createTerm(Junctor.AND, 
						tf.createTerm(Junctor.TRUE), 
						tf.createTerm(Junctor.FALSE));
		
		ImmutableArray<TermLabel> labels = new ImmutableArray<TermLabel>(
		      ParameterlessTermLabel.LOOP_BODY_LABEL);
		
		Term labeledTerm = 
				tf.createTerm(Junctor.AND, 
						tf.createTerm(Junctor.TRUE), 
						tf.createTerm(Junctor.FALSE), labels);
				
		assertFalse("Labeled and unlabeled terms must not be equal", labeledTerm.equals(unlabeledTerm));
		assertFalse("Labeled and unlabeled terms must not be equal", unlabeledTerm.equals(labeledTerm));
	}

	/**
	 * Tests {@link Term#hasLabels()}, {@link Term#hasLabels()} and
	 * {@link Term#containsLabel(TermLabel)}.
	 */
	public void testGetHasAndContainsLabels() {
	   // Create terms
	   Term unlabled = services.getTermBuilder().tt();
	   SymbolicExecutionTermLabel sedLabel = new SymbolicExecutionTermLabel(1);
	   SymbolicExecutionTermLabel anotherSedLabel = new SymbolicExecutionTermLabel(2);
	   Term oneLabel = services.getTermBuilder().label(unlabled, sedLabel);
	   Term oneLabelChanged = services.getTermBuilder().label(oneLabel, ParameterlessTermLabel.LOOP_BODY_LABEL);
	   Term twoLabels = services.getTermBuilder().label(unlabled, new ImmutableArray<TermLabel>(ParameterlessTermLabel.LOOP_BODY_LABEL, sedLabel));
	   // Test unlabled
	   assertFalse(unlabled.hasLabels());
	   assertNotNull(unlabled.getLabels());
	   assertEquals(0, unlabled.getLabels().size());
	   assertFalse(unlabled.containsLabel(sedLabel));
      assertFalse(unlabled.containsLabel(ParameterlessTermLabel.LOOP_BODY_LABEL));
      assertFalse(unlabled.containsLabel(anotherSedLabel));
		// Test oneLabel
      assertTrue(oneLabel.hasLabels());
      assertNotNull(oneLabel.getLabels());
      assertEquals(1, oneLabel.getLabels().size());
      assertSame(sedLabel, oneLabel.getLabels().get(0));
      assertTrue(oneLabel.containsLabel(sedLabel));
      assertFalse(oneLabel.containsLabel(ParameterlessTermLabel.LOOP_BODY_LABEL));
      assertFalse(oneLabel.containsLabel(anotherSedLabel));
      // Test oneLabledAgain
      assertTrue(oneLabelChanged.hasLabels());
      assertNotNull(oneLabelChanged.getLabels());
      assertEquals(1, oneLabelChanged.getLabels().size());
      assertSame(ParameterlessTermLabel.LOOP_BODY_LABEL, oneLabelChanged.getLabels().get(0));
      assertFalse(oneLabelChanged.containsLabel(sedLabel));
      assertTrue(oneLabelChanged.containsLabel(ParameterlessTermLabel.LOOP_BODY_LABEL));
      assertFalse(oneLabelChanged.containsLabel(anotherSedLabel));
      // Test twoLabels
      assertTrue(twoLabels.hasLabels());
      assertNotNull(twoLabels.getLabels());
      assertEquals(2, twoLabels.getLabels().size());
      assertSame(ParameterlessTermLabel.LOOP_BODY_LABEL, twoLabels.getLabels().get(0));
      assertSame(sedLabel, twoLabels.getLabels().get(1));
      assertTrue(twoLabels.containsLabel(sedLabel));
      assertTrue(twoLabels.containsLabel(ParameterlessTermLabel.LOOP_BODY_LABEL));
      assertFalse(twoLabels.containsLabel(anotherSedLabel));
	}
}