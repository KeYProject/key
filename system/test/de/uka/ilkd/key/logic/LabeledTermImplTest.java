// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic;

import junit.framework.TestCase;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.op.Junctor;

public class LabeledTermImplTest extends TestCase {

	public void testEqualsLabelOnTop() {
		Term unlabeledTerm = 
				TermFactory.DEFAULT.createTerm(Junctor.AND, 
						TermFactory.DEFAULT.createTerm(Junctor.TRUE), 
						TermFactory.DEFAULT.createTerm(Junctor.FALSE));
		
		ImmutableArray<ITermLabel> labels = new ImmutableArray<ITermLabel>(
				LoopBodyTermLabel.INSTANCE);
		
		Term labeledTerm = 
				TermFactory.DEFAULT.createTerm(Junctor.AND, 
						TermFactory.DEFAULT.createTerm(Junctor.TRUE), 
						TermFactory.DEFAULT.createTerm(Junctor.FALSE), labels);
				
		assertFalse("Labeled and unlabeled terms must not be equal", labeledTerm.equals(unlabeledTerm));
		assertFalse("Labeled and unlabeled terms must not be equal", unlabeledTerm.equals(labeledTerm));
	}

	/**
	 * Tests {@link Term#hasLabels()}, {@link Term#hasLabels()} and
	 * {@link Term#containsLabel(ITermLabel)}.
	 */
	public void testGetHasAndContainsLabels() {
	   // Create terms
	   Term unlabled = TermBuilder.DF.tt();
	   SymbolicExecutionTermLabel sedLabel = new SymbolicExecutionTermLabel(1);
      SymbolicExecutionTermLabel anotherSedLabel = new SymbolicExecutionTermLabel(2);
	   Term oneLabel = TermBuilder.DF.label(unlabled, sedLabel);
	   Term oneLabelChanged = TermBuilder.DF.label(oneLabel, LoopBodyTermLabel.INSTANCE);
	   Term twoLabels = TermBuilder.DF.label(unlabled, new ImmutableArray<ITermLabel>(LoopBodyTermLabel.INSTANCE, sedLabel));
	   // Test unlabled
	   assertFalse(unlabled.hasLabels());
	   assertNotNull(unlabled.getLabels());
	   assertEquals(0, unlabled.getLabels().size());
	   assertFalse(unlabled.containsLabel(sedLabel));
      assertFalse(unlabled.containsLabel(LoopBodyTermLabel.INSTANCE));
      assertFalse(unlabled.containsLabel(anotherSedLabel));
		// Test oneLabel
      assertTrue(oneLabel.hasLabels());
      assertNotNull(oneLabel.getLabels());
      assertEquals(1, oneLabel.getLabels().size());
      assertSame(sedLabel, oneLabel.getLabels().get(0));
      assertTrue(oneLabel.containsLabel(sedLabel));
      assertFalse(oneLabel.containsLabel(LoopBodyTermLabel.INSTANCE));
      assertFalse(oneLabel.containsLabel(anotherSedLabel));
      // Test oneLabledAgain
      assertTrue(oneLabelChanged.hasLabels());
      assertNotNull(oneLabelChanged.getLabels());
      assertEquals(1, oneLabelChanged.getLabels().size());
      assertSame(LoopBodyTermLabel.INSTANCE, oneLabelChanged.getLabels().get(0));
      assertFalse(oneLabelChanged.containsLabel(sedLabel));
      assertTrue(oneLabelChanged.containsLabel(LoopBodyTermLabel.INSTANCE));
      assertFalse(oneLabelChanged.containsLabel(anotherSedLabel));
      // Test twoLabels
      assertTrue(twoLabels.hasLabels());
      assertNotNull(twoLabels.getLabels());
      assertEquals(2, twoLabels.getLabels().size());
      assertSame(LoopBodyTermLabel.INSTANCE, twoLabels.getLabels().get(0));
      assertSame(sedLabel, twoLabels.getLabels().get(1));
      assertTrue(twoLabels.containsLabel(sedLabel));
      assertTrue(twoLabels.containsLabel(LoopBodyTermLabel.INSTANCE));
      assertFalse(twoLabels.containsLabel(anotherSedLabel));
	}
}