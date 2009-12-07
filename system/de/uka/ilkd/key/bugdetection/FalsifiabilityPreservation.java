package de.uka.ilkd.key.bugdetection;

import java.util.Iterator;
import java.util.Vector;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableMapEntry;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**Implementation of the technique described in 
 * Christoph Gladisch. Could we have chosen a better Loop Invariant or Method Contract? In Proc. TAP 2009
 * @author gladisch 
 * */
public class FalsifiabilityPreservation {
    
    
    
    /**Traverse a proof branch from node {@code n} towards the root and collect
     * Falsifiability preservation conditions at occurrences of loop invariant 
     * and method contract rule applications. The root may not be reached
     * (under certain circumstances e.g. when passing 1st or 2nd branch of a contract rule) */
    public Vector<FPCondition> collectFPConditions(Node n){
	Vector<FPCondition> res = new Vector();
	while(!n.root()){
	    Node parent = n.parent();
	    RuleApp ruleApp = parent.getAppliedRuleApp();
	    if(ruleApp!=null){
		Name parentRuleAppName = ruleApp.rule().name();
		if(parentRuleAppName.toString().startsWith("whileInv")){
		    	PosTacletApp tacletApp = (PosTacletApp)ruleApp;
			System.out.println("\nparentNode:"+parent.serialNr()+" RuleApp:"+parentRuleAppName);
			System.out.println("childNode:"+n.serialNr()+ " SibblingNr:"+n.siblingNr()+ " Name:"+n.name()+ " NodeInfo.branchlabel:"+n.getNodeInfo().getBranchLabel());
			
			SVInstantiations svInst = tacletApp.instantiations();
			Iterator<ImmutableMapEntry<SchemaVariable,InstantiationEntry>> entryIt = svInst.pairIterator();
			while(entryIt.hasNext()){
			    System.out.println(entryIt.next());
			}
			String s=svInst.toString();
			//System.out.println("------Instantiations-----\n"+s);
			s=tacletApp.posInOccurrence().toString();
			//System.out.println("-------posInOccurrence-------\n"+s);
			s = tacletApp.toString();
			//System.out.println("-------ruleApp------\n"+s);			    
			System.out.println("------ new formulas in node "+n.serialNr()+" -------");
			Vector<ConstrainedFormula> vec = findNewFormulasInSucc(n);
			for(ConstrainedFormula cf:vec){
			    System.out.println(cf);
			}
		}
	    }
	    n=parent;
	}
	return res;
    }
    
    /**Returns formulas that are in succedent of node {@code n} that are not present in its 
     * parent node's succedent. This is a hack in order to find out what formulas have 
     * been added by rule application
     * @author gladisch */
    private Vector<ConstrainedFormula> findNewFormulasInSucc(Node n){
	Vector<ConstrainedFormula> res = new Vector<ConstrainedFormula>();
	if(n==null){ return res;}
	final Node parent = n.parent();
	Semisequent pSucc=null;
	if(parent!=null){
	    pSucc = parent.sequent().succedent();
	}

	final Iterator<ConstrainedFormula> succIt =n.sequent().succedent().toList().iterator();
	while(succIt.hasNext()){
	    ConstrainedFormula cf = succIt.next();
	    if(pSucc==null || !pSucc.contains(cf)){
		res.add(cf);
	    }
	}
	return res;
    }
    
    
    class FPCondition {
	/**The falsifiability preservation is considered between this node and its parent node.
	 * Thus this node is the branch of the rule application in focus*/
	public Node node;
	
	/**The formula to be proved in order to guarantee falsifiability preservation.
	 * This can be the Special Falsifiability Preservation condition (SFP) */
	public Term fpCond;
    }
}
