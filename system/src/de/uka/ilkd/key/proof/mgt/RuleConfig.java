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


package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Choice;

public class RuleConfig {

    private ImmutableSet<Choice> activatedChoices;
   
    public RuleConfig(ImmutableSet<Choice> ruleOpts) {
	this.activatedChoices=ruleOpts;
    }
   
    public ImmutableSet<Choice> getChoices() {
	return activatedChoices;
    }

    public boolean equals(Object o) {
	if (!(o instanceof RuleConfig)) return false;
	return activatedChoices.equals(((RuleConfig)o).getChoices());
    }

    public int hashCode() {
	return activatedChoices.hashCode();
    }

    public String description() {
	return activatedChoices.toString();
    }
}
