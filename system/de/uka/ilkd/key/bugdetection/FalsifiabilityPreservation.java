package de.uka.ilkd.key.bugdetection;

import java.util.Vector;

import de.uka.ilkd.key.bugdetection.BugDetector.UnhandledCase;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;

/**Implementation of the technique described in 
 * Christoph Gladisch. Could we have chosen a better Loop Invariant or Method Contract? In Proc. TAP 2009
 * <br>
 * This class represents the falsifiability preservation of a branch
 * @author gladisch 
 * */
public class FalsifiabilityPreservation {
    
    /**First, second, and third branch of contract rules. Not that this enumeration is
     * according to the paper "Could we have chosen a better Loop Invariant or Method Contract? In Proc. TAP 2009".
     * The enumeration of the real branches created by KeY may be different. E.g. THIRD branch of
     * method contract rule is in KeY the second branch. */
    public enum BranchType {FIRST, SECND, THRID};
    public enum RuleType {LOOP_INV, METH_CONTR};
    
    /**Gives access to some utilities like Services and MsgMgt (MessageManagement) */
    final protected BugDetector bd;
    /**The branch between {@code branchNode} and the root node is considered by {@code this} object.
     * This field identifies the branch that is considered here. */
    final protected Node branchNode;
    
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
     * (under certain circumstances e.g. when passing 1st or 2nd branch of a contract rule) */
    public Vector<FPCondition> collectFPConditions(){
	//Save the last known node of the branch. Alternatively, we could iterate 
	//to select a deeper node if possible. Todo: The user should be notified if there are deeper nodes.
	Node n = branchNode; 
	Vector<FPCondition> res = new Vector();
	while(!n.root()){
	    Node parent = n.parent();
	    RuleApp ruleApp = parent.getAppliedRuleApp();
	    if(ruleApp!=null){
		Name parentRuleAppName = ruleApp.rule().name();
		if(parentRuleAppName.toString().startsWith("whileInv")){
		    //First check if an FPCondition is already created for this node.
		    FPCondition fpc=getFPCondition(n);
		    if(fpc==null){
        		    //If an FPCondition was not yet associated with the current node, then create new ones
        
        		    final RuleType ruleType = RuleType.LOOP_INV;
        		    final BranchType branchType = getBranchType(ruleType,n);
        		    if(branchType == BranchType.THRID){
        			fpc = new SFPCondition(n, branchNode, ruleType, branchType, bd);
        		    }else{
        			fpc = new FPCondition(n,ruleType, branchType, bd);
        		    }
        		    fpc.addFPCListener(this);
        		    fpc.constructFPC();
        		    branchNode.addSMTandFPData(fpc);
        		    if(getFPCondition(branchNode)!=fpc){
        			throw new RuntimeException();
        		    }
        		    fpc.check();

		    }
		    res.add(fpc);

		    
//		    	PosTacletApp tacletApp = (PosTacletApp)ruleApp;
//			System.out.println("\nparentNode:"+parent.serialNr()+" RuleApp:"+parentRuleAppName);
//			
//			SVInstantiations svInst = tacletApp.instantiations();
//			Iterator<ImmutableMapEntry<SchemaVariable,InstantiationEntry>> entryIt = svInst.pairIterator();
//			while(entryIt.hasNext()){
//			    System.out.println(entryIt.next());
//			}
//			String s=svInst.toString();
//			//System.out.println("------Instantiations-----\n"+s);
//			s=tacletApp.posInOccurrence().toString();
//			//System.out.println("-------posInOccurrence-------\n"+s);
//			s = tacletApp.toString();
//			//System.out.println("-------ruleApp------\n"+s);			    
//			System.out.println("------ new formulas in node "+n.serialNr()+" -------");
//			Vector<ConstrainedFormula> vec = findNewFormulasInSucc(n);
//			for(ConstrainedFormula cf:vec){
//			    System.out.println(cf);
//			}
		}
	    }
	    n=parent;
	}
	return res;
    }
    
    /**@param n is the child node of the loop invariant or method contract rule application
     * @see BranchType */
    private BranchType getBranchType(RuleType rt, Node n){
	BranchType res;
	if(rt==RuleType.LOOP_INV){
	    //System.out.println("childNode:"+n.serialNr()+ " SibblingNr:"+n.siblingNr()+ " Name:"+n.name()+ " NodeInfo.branchlabel:"+n.getNodeInfo().getBranchLabel());
	    if(n.siblingNr()==2||n.getNodeInfo().getBranchLabel().equalsIgnoreCase("Use Case")){
		res = BranchType.THRID;
		if(!(n.siblingNr()==2 && n.getNodeInfo().getBranchLabel().equalsIgnoreCase("Use Case"))){
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
     * @return the FPCondition associated with the given node or null if it does not exist. */
    public FPCondition getFPCondition(Node n){
	    Vector<Object> smtAndFPData = n.getSMTandFPData();
	    if(smtAndFPData!=null){
		for(Object o:smtAndFPData){
		    if(o instanceof FPCondition){
			return (FPCondition)o;
		    }
		}
	    }	
	    return null;
    }
    
    /** Call this method to notify this receiver object that the
     * falsifiability preservation condition has been updated. 
     * A caller of this method is in {@code FPCondition}.
     * Note: the node is accessible via fpc.node or fpc.parent*/
    public void fpcUpdate(FPCondition fpc){
	System.out.println("FP for node "+fpc.node.serialNr()+" is "+fpc.isValid());
    }
    
    /**This method is queried, e.g., by {@code SMTResultsAndBugDetectionDialog.updateTableForNode()} 
     * @return the node closest to the root up to which falsifiability is preserved,
     * when starting from the {@code branchNode}. */
    public Node get_Upto_Node(){
	//TODO: the branch has to be traversed and FPConditions have to be checked if they are valid.
	return branchNode;
    }
    
    private void warning(String s, int severity){
	bd.msgMgt.warning(s, severity);
    }
    
    

}
