package de.uka.ilkd.key.bugdetection;

import java.util.Vector;

import de.uka.ilkd.key.bugdetection.BugDetector.UnhandledCase;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;

/**Implementation of the technique described in<br> 
 * Christoph Gladisch. Could we have chosen a better Loop Invariant or Method Contract? In Proc. TAP 2009
 * <br>
 * This class represents the falsifiability preservation of a branch.
 * Instances of this class are associated with Nodes in the hashmap {@code Proof.nodeToSMTandFPData}
 * @author gladisch 
 * */
public class FalsifiabilityPreservation {
    
    /**First, second, and third branch of contract rules. Note that this enumeration is
     * according to the paper "Could we have chosen a better Loop Invariant or Method Contract? In Proc. TAP 2009".
     * The enumeration of the real branches created by KeY may be different. E.g. THIRD branch of
     * method contract rule is in KeY the second branch. */
    public enum BranchType {FIRST, SECND, THRID};
    
    /**Critical rule types (for which falsifiability preservation shall be checked) are: 
     * loop invariant and method contract rules. TODO hiding/weakening rules. */
    public enum RuleType {LOOP_INV, METH_CONTR, HIDE_LEFT, HIDE_RIGHT};
    
    /**Gives access to some utilities like Services and MsgMgt (MessageManagement) */
    final protected BugDetector bd;
    
    /**The branch between {@code branchNode} and the root node is considered by {@code this} object.
     * This field identifies the branch that is considered here. */
    final protected Node branchNode;
    
    /**The order of the names is important. */
    public final static String[] criticalRuleNames = {"whileInv","Use Operation Contract","hide_left", "hide_right"};
    
    /**Warning this constructor has a side-effect on the proof object. It associates
     * the newly create object with the given branchNode
     * @param branchNode The branch between {@code branchNode} and the root node is considered by {@code this} object.
     * This field identifies the branch that is considered here.
     * */
    public FalsifiabilityPreservation(BugDetector bd, Node branchNode){
	this.bd = bd;
	this.branchNode = branchNode;
	branchNode.addSMTandFPData(this);
	if(!branchNode.getSMTandFPData().contains(this)){
	    throw new RuntimeException("FalsifiabilityPreservation cannot associate itself with the node:"+branchNode.serialNr());
	}
    }
    
    
    
    /**Traverse a proof branch from node {@code n} towards the root and collect
     * Falsifiability preservation conditions at occurrences of loop invariant 
     * and method contract rule applications. The root may not be reached
     * under certain circumstances e.g. when passing 1st or 2nd branch of a contract rule. 
     * Warning: This method has a side-effect on the Proof object. Nodes are associated with FPConditions*/
    public Vector<FPCondition> collectFPConditions(){
	//Save the last known node of the branch. Alternatively, we could iterate 
	//to select a deeper node if possible. Todo: The user should be notified if there are deeper nodes.
	Node n = branchNode; 
	Vector<FPCondition> res = new Vector();
	while(!n.root()){
	    Node parent = n.parent();
	    RuleApp ruleApp = parent.getAppliedRuleApp();
	    if(ruleApp!=null && isCriticalRule(ruleApp.rule())){
		//First check if an FPCondition is already created for this node.
		FPCondition fpc=getFPCondition(n);
		if (fpc == null) {
		    // If an FPCondition was not yet associated with the current node, then create new ones
		    Name parentRuleAppName = ruleApp.rule().name();
		    final RuleType ruleType;
		    if (parentRuleAppName.toString().startsWith(criticalRuleNames[0])) { // Loop Invariant
			ruleType = RuleType.LOOP_INV;
		    } else if (parentRuleAppName.toString().startsWith(criticalRuleNames[1])) {// Method Contract
			ruleType = RuleType.METH_CONTR;
		    } else if (parentRuleAppName.toString().startsWith(criticalRuleNames[2])) {// Hide Left
			ruleType = RuleType.HIDE_LEFT;
		    } else if (parentRuleAppName.toString().startsWith(criticalRuleNames[3])) {// Hide Left
			ruleType = RuleType.HIDE_RIGHT;
		    } else{
			throw new RuntimeException(
			        "Case distinctions are missing a case that is considered by isCriticalRule().");
		    }
		    if(ruleType==RuleType.LOOP_INV || ruleType==RuleType.METH_CONTR){
			final BranchType branchType = getBranchType(ruleType, n);
			if (branchType == BranchType.THRID) {
			    fpc = new SFPCondition(n, this, ruleType,branchType, bd);
			} else {
			    fpc = new FPConditionFALSE(n, ruleType, branchType, bd);
			}
		    }else if(ruleType==RuleType.HIDE_LEFT || ruleType==RuleType.HIDE_RIGHT){
			//The branch type has no meaning here
			fpc = new FPCondition(n, ruleType, BranchType.FIRST, bd);
		    }
		    fpc.constructFPC();
		}
		fpc.addFPCListener(this);
		res.add(fpc);
	    }
	    n=parent;
	}
	return res;
    }
    
    public static boolean isCriticalRule(Rule r){
	String name = r.name().toString();
	for(String s:criticalRuleNames){
	    if(name.startsWith(s)){
		return true;
	    }
	}
	return false;
    }
    
    /**@param n is the child node of the loop invariant or method contract rule application
     * @see BranchType */
    private BranchType getBranchType(RuleType rt, Node n){
	BranchType res;
	int sibNr = n.siblingNr();
	String bLabel = "";
	try{ 
	    bLabel = n.getNodeInfo().getBranchLabel();
	}catch(Exception e){ }
	
	if(rt==RuleType.LOOP_INV){
	    //System.out.println("childNode:"+n.serialNr()+ " SibblingNr:"+n.siblingNr()+ " Name:"+n.name()+ " NodeInfo.branchlabel:"+n.getNodeInfo().getBranchLabel());
	    if(sibNr==0||bLabel.equalsIgnoreCase("Invariant Initially Valid")){
		res = BranchType.FIRST;
		if(!(sibNr==0 && bLabel.equalsIgnoreCase("Invariant Initially Valid"))){
		    warning("Recognizing the branch type of node "+n.serialNr()+" may have failed.",2);
		}
	    }else if(sibNr==1||bLabel.equalsIgnoreCase("Body Preserves Invariant")){
		res = BranchType.SECND;
		if(!(sibNr==1 && bLabel.equalsIgnoreCase("Body Preserves Invariant"))){
		    warning("Recognizing the branch type of node "+n.serialNr()+" may have failed.",2);
		}
	    }else if(sibNr==2||bLabel.equalsIgnoreCase("Use Case")){
		res = BranchType.THRID;
		if(!(sibNr==2 && bLabel.equalsIgnoreCase("Use Case"))){
		    warning("Recognizing the branch type of node "+n.serialNr()+" may have failed.",2);
		}
	    }else{
		throw new UnhandledCase("getBranchType("+rt+", "+n.serialNr()+")");
	    }
	}else if(rt==RuleType.METH_CONTR){
	    if(sibNr ==0 || bLabel.equalsIgnoreCase("Pre")){
		res = BranchType.FIRST;
		if(!(sibNr==0 && bLabel.equalsIgnoreCase("Pre"))){
		    warning("Recognizing the branch type of node "+n.serialNr()+" may have failed.",2);
		}
	    }else if(sibNr ==1 || bLabel.equalsIgnoreCase("Post")){
		res = BranchType.THRID;
		if(!(sibNr==1 && bLabel.equalsIgnoreCase("Post"))){
		    warning("Recognizing the branch type of node "+n.serialNr()+" may have failed.",2);
		}
	    }else{
		throw new UnhandledCase("getBranchType("+rt+", "+n.serialNr()+")");
	    }
	    
	}else{
	    throw new UnhandledCase("getBranchType("+rt+", "+n.serialNr()+")");
	}
	return res;
    }
    
    
    /**A utility method.
     * @return the FPCondition associated with the given node and with this branch. Null is returned otherwise. */
    public  FPCondition getFPCondition(Node n){
	    Vector<Object> smtAndFPData = n.getSMTandFPData();
	    if(smtAndFPData!=null){
		for(Object o:smtAndFPData){
		    if(o instanceof FPCondition){
			FPCondition fpc = (FPCondition)o;
			if(fpc.belongsTo(this)){
			    return (FPCondition)o;
			}
		    }
		}
	    }	
	    return null;
    }
    
    /** Call this method to notify this receiver object that the
     * falsifiability preservation condition has been updated. 
     * A caller of this method is in {@code FPCondition.validityUpdate()}.
     * Note: the node is accessible via fpc.node or fpc.parent*/
    public void fpcUpdate(FPCondition fpc){
	System.out.println("FP for node "+fpc.node.serialNr()+" is "+fpc.isValid());
	branchNode.proof().fireSmtDataUpdate(branchNode);
    }
    
    /**This method is queried, e.g., by {@code SMTResultsAndBugDetectionDialog.updateTableForNode()}
     * The event is triggered when calling {@code fpcUpdate}. 
     * @return the node closest to the root up to which falsifiability is preserved,
     * when starting from the {@code branchNode}. */
    public Node get_Upto_Node(){
	Node n = branchNode; 
	while(!n.root()){
	    Node parent = n.parent();
	    RuleApp ruleApp = parent.getAppliedRuleApp();
	    if(ruleApp!=null && isCriticalRule(ruleApp.rule())){
		FPCondition fpc=getFPCondition(n);
//		if(fpc==null){
//		    throw new RuntimeException("The node "+n.serialNr()+" should already be associate with a FPCondition. Maybe the initialization is brocken.");
//		}
		if(fpc==null || fpc.isValid()==null || !fpc.isValid()){
		    //If falsifiability preservation is unknown or false, then this is the point up to which we know that fp is preserved.
		    return n;
		}
	    }
	    n = parent;
	}
	return n;
    }
    
    /**@return the first FPCondition that is not provend to be valid when traversing 
     * from the branch node towards the root. Null is returned if there is no FPCondition
     * or if all FPConditions are valid.
     * <br> Note that this method is a bit different than get_Upto_Node because this method
     * may return null whereas get_Upto_Node returns a node != null.*/
    protected FPCondition getUptoFPCondition(){
	Node n = branchNode; 
	while(!n.root()){
	    Node parent = n.parent();
	    RuleApp ruleApp = parent.getAppliedRuleApp();
	    if(ruleApp!=null && isCriticalRule(ruleApp.rule())){
		FPCondition fpc=getFPCondition(n);
		if(fpc==null){
		    throw new RuntimeException("The node "+n.serialNr()+" should already be associate with a FPCondition. Maybe the initialization is brocken.");
		}
		if( fpc.isValid()==null || !fpc.isValid()){
		    //If falsifiability preservation is unknown or false, then this is the point up to which we know that fp is preserved.
		    return fpc;
		}
	    }
	    n = parent;
	}

	return null;
    }
    
    /**@param falsifiable determins whether the branchNode is falsifiable. Null == unknown. 
     * @return a message for the user that explains the meaning of this particular
     * falsifiability preservation situation. This message is displayed by the 
     * {@code SMTResultsAndBugDetectionDialog} */
    public String getMessage(Boolean falsifiable){
	Node uptoNode = get_Upto_Node();
	String standard = "Falsifiability is preserved from node "+ branchNode.serialNr()+
				" up to "+ (uptoNode.root()?"the root node":"node "+uptoNode.serialNr());
	if(falsifiable == null){
	    return standard+". \n Use SMT solvers to check if node "+branchNode.serialNr()+" is valid or falsifiable.";
	}else if(falsifiable == true){
	    if(uptoNode.root()){
		return "The target program has a bug on the selected trace (proof branch).\n"+
			"This is because the branch node is falsifiable and \n"+standard;
	    }else{
		FPCondition upto = getUptoFPCondition();
		if(upto==null){
		    return "Strange this case should have already be caught. It means the falsifiability is preserved upto the root node.";
		}else if(upto.branchType == BranchType.FIRST){
		    if(upto.ruleType == RuleType.LOOP_INV){
			return "The loop invariant applied at node "+uptoNode.parent().serialNr()+" is not preserved a the beginning of the loop.";
		    }else if(upto.ruleType == RuleType.METH_CONTR){
			return "The precondition of the method contract applied at node "+uptoNode.parent().serialNr()+" is not satisfied before the method call";
		    }else{
			return standard;
		    }
		}else if(upto.branchType == BranchType.SECND){
		    if(upto.ruleType == RuleType.LOOP_INV){
			return "The loop invariant applied at node "+uptoNode.parent().serialNr()+" is not preserved during loop iteration.";
		    }else if(upto.ruleType == RuleType.METH_CONTR){
			return "The method contract applied at node "+uptoNode.parent().serialNr()+" is not correct.";
		    }else{
			return standard;
		    }
		}else{
		    return standard;
		}
	    }
	}else{
	    return "The branch is closed.";
	}
	//return "Warning: unexpected case";
    }
    

    private void warning(String s, int severity){
	bd.msgMgt.warning(s, severity);
    }
    
    

    public Services getServices(){
	return branchNode.proof().getServices();
    }
}
