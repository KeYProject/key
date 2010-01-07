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