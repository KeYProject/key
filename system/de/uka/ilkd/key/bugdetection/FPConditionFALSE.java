// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.bugdetection;

import de.uka.ilkd.key.bugdetection.FalsifiabilityPreservation.BranchType;
import de.uka.ilkd.key.bugdetection.FalsifiabilityPreservation.RuleType;
import de.uka.ilkd.key.proof.Node;

public class FPConditionFALSE extends FPCondition{

	public FPConditionFALSE(Node node, RuleType ruleType,
            BranchType branchType, BugDetector bd) {
	    super(node, ruleType, branchType, bd);
	    // TODO Auto-generated constructor stub
    }
	
	public void check(){ }
	
	public Boolean isValid(){return false;}
	
	public void constructFPC(){ };
	
}
