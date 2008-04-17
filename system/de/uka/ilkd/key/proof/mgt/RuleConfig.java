// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.logic.SetOfChoice;

public class RuleConfig {

    private SetOfChoice activatedChoices;
   
    public RuleConfig(SetOfChoice ruleOpts) {
	this.activatedChoices=ruleOpts;
    }
   
    public SetOfChoice getChoices() {
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
