package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.rule.Taclet;

public class TacletFilterCloseGoal extends TacletFilter {
	
	public final static TacletFilterCloseGoal INSTANCE = 
            new TacletFilterCloseGoal ();
	
	private TacletFilterCloseGoal () {
	}

	protected boolean filter(Taclet taclet) {
		return taclet.goalTemplates().size() == 0;
	}

}
