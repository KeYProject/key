package de.uka.ilkd.key.bugdetection;

import java.util.Iterator;
import java.util.Vector;

import de.uka.ilkd.key.bugdetection.BugDetector.MsgMgt;
import de.uka.ilkd.key.bugdetection.BugDetector.UnhandledCase;
import de.uka.ilkd.key.bugdetection.FalsifiabilityPreservation.BranchType;
import de.uka.ilkd.key.bugdetection.FalsifiabilityPreservation.RuleType;
import de.uka.ilkd.key.collection.ImmutableMapEntry;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AnonymousUpdate;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.Update;

/**Falsifiability preservation condition and informations for a node */
public class FPCondition {
	/**The falsifiability preservation is considered between this node and its parent node.
	 * Thus this node is the branch of the rule application in focus*/
	public final Node node;
	
	public final BranchType branchType;
	public final RuleType ruleType;
	
	/**The formula to be proved in order to guarantee falsifiability preservation.
	 * This can be the Special Falsifiability Preservation condition (SFP) */
	public Term fpCond;
	
	/**the parent {@code node} */
	protected Node parent;
	/**Gives access to some utilities like Services and MsgMgt (MessageManagement) */
	protected final BugDetector bd;
	protected TermBuilder tb = TermBuilder.DF;

	
	public FPCondition(Node node, RuleType ruleType, BranchType branchType, BugDetector bd){
	    this.node = node;
	    this.ruleType = ruleType;
	    this.branchType = branchType;
	    this.bd = bd;
	    parent = node.parent();
	}
	
	/**Call this method after initialization of this object to construct and 
	 * further initilizse the object the falsifiability preservation condition*/
	public void constructFPC(){
	    final Vector<ConstrainedFormula> cfs = findNewFormulasInSucc(node);
	    final ConstrainedFormula cf 	  = pickRelevantFormula(cfs);
	    if(branchType == BranchType.THRID){
		throw new UnhandledCase("Handling of THIRD branch is not implemented in this FPCondition. Use SFPCondition instead.");
	    }else{
		throw new UnhandledCase("constructFPC does not handle branch type:"+branchType+" I think that FALSE should be returned as FP-condition.");
	    }
	}
	
	/**
	 * Returns formulas that are in succedent of node {@code n} that are not
	 * present in its parent node's succedent. This is a hack in order to
	 * find out what formulas have been added by rule application
	 * 
	 * @author gladisch
	 */
	protected Vector<ConstrainedFormula> findNewFormulasInSucc(Node n) {
	    Vector<ConstrainedFormula> res = new Vector<ConstrainedFormula>();
	    if (n == null) {
		return res;
	    }
	    final Node parent = n.parent();
	    Semisequent pSucc = null;
	    if (parent != null) {
		pSucc = parent.sequent().succedent();
	    }

	    final Iterator<ConstrainedFormula> succIt = 
				n.sequent().succedent().toList().iterator();
	    while (succIt.hasNext()) {
		ConstrainedFormula cf = succIt.next();
		if (pSucc == null || !pSucc.contains(cf)) {
		    res.add(cf);
		}
	    }
	    return res;
	}

	/**If findNewFormulasInSucc returns multiple formulas, then use this method
	 * to pick the formula that looks like the one to be the main prove obligation (that contains e.g. the program). 
	 * Warning this method uses heuristics to determine the right formula*/
	protected ConstrainedFormula pickRelevantFormula(Vector<ConstrainedFormula> cfs){
	    if(cfs.size()==1){
		return cfs.firstElement();
	    }else if(cfs.size()==0){
		return null;
	    }else {
		warning("pickRelevantFormula() uses heuristics to determine the relevant formula. This may be unsound.",0);
		int[] score = new int[cfs.size()];
		int i =0;
		for(ConstrainedFormula cf:cfs){
		    Term f = cf.formula();
		    Operator op = f.op();
		    if(f.executableJavaBlock()!=null){
			score[i]+=100;
		    }
		    if(op instanceof Modality){
			score[i]+=10;
		    }
		}
		int max=0;
		for(int j:score){
		    if(score[j]>score[max]) max = j;
		}
		return cfs.get(score[max]);
	    }
	}
	

	protected void warning(String s, int severity){
	    bd.msgMgt.warning(s, severity);
	}
	
}