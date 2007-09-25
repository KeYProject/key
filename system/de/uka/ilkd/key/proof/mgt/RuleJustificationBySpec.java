// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.mgt;

import java.util.List;

public class RuleJustificationBySpec extends LemmaRuleJustification{

    private Contract ct;

    public RuleJustificationBySpec(Contract ms) {
	this.ct = ms;
    }

    public Contract getContract() {
	return ct;
    }
    
    public List getProofList() {
	return getContract().getProofs();
    }

    public String toString() {
	return "contract justification "+ct;
    }
}
