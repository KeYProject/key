package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.op.Junctor;
import junit.framework.TestCase;

public class LabeledTermImplTest extends TestCase {

	public void testEqualsLabelOnTop() {
		Term unlabeledTerm = 
				TermFactory.DEFAULT.createTerm(Junctor.AND, 
						TermFactory.DEFAULT.createTerm(Junctor.TRUE), 
						TermFactory.DEFAULT.createTerm(Junctor.FALSE));
		
		ImmutableArray<ITermLabel> labels = new ImmutableArray<ITermLabel>(
				SymbolicExecutionLabel.INSTANCE);
		
		Term labeledTerm = 
				TermFactory.DEFAULT.createTerm(Junctor.AND, 
						TermFactory.DEFAULT.createTerm(Junctor.TRUE), 
						TermFactory.DEFAULT.createTerm(Junctor.FALSE), labels);
				
		assertFalse("Labeled and unlabeled terms must not be equal", labeledTerm.equals(unlabeledTerm));
		assertFalse("Labeled and unlabeled terms must not be equal", unlabeledTerm.equals(labeledTerm));
	}

	public void testGetLabels() {
		//fail("Not yet implemented"); // TODO
	}

	public void testContainsLabel() {
		//fail("Not yet implemented"); // TODO
	}

}
