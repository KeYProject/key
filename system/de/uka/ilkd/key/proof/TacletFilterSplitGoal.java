package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.rule.Taclet;

public class TacletFilterSplitGoal extends TacletFilter {
	
	public final static TacletFilterSplitGoal INSTANCE = new TacletFilterSplitGoal ();
	
	private TacletFilterSplitGoal () {
	}

	protected boolean filter(Taclet taclet) {
		return taclet.goalTemplates().size() > 1;
	}

}
