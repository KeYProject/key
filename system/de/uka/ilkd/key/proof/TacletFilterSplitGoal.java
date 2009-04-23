// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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
