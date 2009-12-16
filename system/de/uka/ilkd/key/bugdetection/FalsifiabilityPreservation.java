package de.uka.ilkd.key.bugdetection;

import java.util.Iterator;
import java.util.Vector;

import de.uka.ilkd.key.bugdetection.BugDetector.MsgMgt;
import de.uka.ilkd.key.bugdetection.BugDetector.UnhandledCase;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableMapEntry;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.UpdateTerm;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.logic.op.*;

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
		    final RuleType ruleType = RuleType.LOOP_INV;
		    final BranchType branchType = getBranchType(ruleType,n);
		    final FPCondition fpc;
		    if(branchType == BranchType.THRID)
			fpc = new SFPCondition(n, branchNode, ruleType, branchType, bd);
		    else
			fpc = new FPCondition(n,ruleType, branchType, bd);

		    fpc.addFPCListener(this);
		    fpc.constructFPC();
		    fpc.check();
		    
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
    
    /** Call this method to notify this receiver object that the
     * falsifiability preservation condition has been updated. 
     * A caller of this method is in {@code FPCondition}.
     * Note: the node is accessible via fpc.node or fpc.parent*/
    public void fpcUpdate(FPCondition fpc){
	System.out.println("FP for node "+fpc.node.serialNr()+" is "+fpc.isValid());
    }
    

    private void warning(String s, int severity){
	bd.msgMgt.warning(s, severity);
    }
    
    

}
