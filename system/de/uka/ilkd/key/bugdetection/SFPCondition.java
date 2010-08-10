// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.bugdetection;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Vector;

import de.uka.ilkd.key.bugdetection.BugDetector.MsgMgt;
import de.uka.ilkd.key.bugdetection.BugDetector.UnhandledCase;
import de.uka.ilkd.key.bugdetection.BugDetector.UnknownCalculus;
import de.uka.ilkd.key.bugdetection.FalsifiabilityPreservation.BranchType;
import de.uka.ilkd.key.bugdetection.FalsifiabilityPreservation.RuleType;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableMapEntry;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.AnonymisingUpdateFactory;
import de.uka.ilkd.key.logic.BasicLocationDescriptor;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.EverythingLocationDescriptor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.LocationDescriptor;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.UpdateFactory;
import de.uka.ilkd.key.logic.op.AnonymousUpdate;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.logic.op.Location;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.BuiltInRuleIndex;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRuleApp;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.OperationContractImpl;
import de.uka.ilkd.key.speclang.SignatureVariablesFactory;
import de.uka.ilkd.key.visualdebugger.watchpoints.WatchPoint;
import de.uka.ilkd.key.visualdebugger.watchpoints.WatchpointPO;

/**Special Falsifiability Preservation Condition as described in the paper
 * <br> 
 * Christoph Gladisch. Could we have chosen a better Loop Invariant or Method Contract? In Proc. TAP 2009
 * <br>
 * Instances of this class are associated with Nodes in the hashmap {@code Proof.nodeToSMTandFPData}
 * @author gladisch */
public class SFPCondition extends FPCondition {
    
    
    private final FalsifiabilityPreservation fp;
    
    /**Formula 2 according to the paper. The SFP formula. The condition if the FIRST and SECOND branches
     * of the contract rule are closed is not expressed here. */
    private Boolean form2isValid=null;

    /**After calling the constructor also call {@code addFPListener()}, {@code constructFPC()}, {@code check()}, {@code validityUpdate}.
     * <p>Warning: this constructor has a side-effect on the Proof-object because it adds the newly created object
     * to the proof; it associates {@code node} with this object. This again triggers a notification to proofTreeListeners
     * that smtAndFPdata has been added. 
     * @param fp the branch that the SFP condition belongs to. Be aware that SFPConditions are not shared
     * between different branches because they differ depending on the last node of a branch. */
    public SFPCondition(Node node, FalsifiabilityPreservation fp, RuleType ruleType, BranchType branchType,
	    BugDetector bd) {
	super(node, ruleType, branchType, bd);
	this.fp = fp;
	node.proof().addProofTreeListener(new ProofTreeListener3());
    }
    
    /**Call this method after the constructor.
     * An FPCondition may be shared by multiple falsifiability preservations of branches, 
     * because multiple branches may share common nodes. 
     * However a special falsifiability preservation condition may belong only to one branch.
     * Adding the same object multiple times is allowed because a set is implemented.*/
    public void addFPCListener(FalsifiabilityPreservation fp){
	if(fp == null){
	    throw new NullPointerException();
	}
	if(fpListeners.contains(fp)){
	    return;
	}
	if(fpListeners.size()>0){
	    throw new RuntimeException("A Special Falsifiability Preservation condition may belong only to one branch.");
	}
	fpListeners.add(fp);
    }
    
    /**
     * Call this method after initialization of this object to construct and
     * further initilizse the object the special falsifiability preservation condition
     */
    public void constructFPC() {
	if (branchType == BranchType.THRID) {
	    ContractAppInfo cInfo=null;
	    if(ruleType == RuleType.LOOP_INV){
		cInfo = ContractAppInfo.LoopInvAppInfo.getContractAppInfo(node);
	    }else if (ruleType == RuleType.METH_CONTR) {
		cInfo = ContractAppInfo.MethContrAppInfo.getContractAppInfo(node);
	    }else{
		throw new RuntimeException("Unexpected ruleType while constructing SFP:"+ruleType);
	    }
	    System.out.println(cInfo);

	    assert cInfo.prefix!=null; 
	    assert cInfo.anon!=null;
	    assert cInfo.contractPost != null;
	    final Location[] locsM0 = new Location[cInfo.anon.locationCount()];
	    final AssignmentPair[] apsM0M1 = new AssignmentPair[cInfo.anon.locationCount()];
	    final LocationDescriptor[] locDescM0 = new LocationDescriptor[locsM0.length];
	    for(int i =0;i<locsM0.length;i++){
		locsM0[i] = cInfo.anon.location(i);
		apsM0M1[i] = cInfo.anon.getAssignmentPair(i);
		locDescM0[i] = new BasicLocationDescriptor(apsM0M1[i].locationAsTerm());
	    }
	    
	        UpdateFactory uf = new UpdateFactory(getServices(), new UpdateSimplifier());
	        AnonymisingUpdateFactory auf = new AnonymisingUpdateFactory(uf);
	        
	        RigidFunction[] functions = auf.createUninterpretedFunctions(locDescM0,getServices());
	        
	        Term M2post = auf.createAnonymisingUpdateTerm ( locDescM0, functions, cInfo.contractPost, getServices());
	        Term UM2post = uf.apply(cInfo.prefix, M2post);
	        
	        HashMap opToOp = new HashMap();
	        for(int i=0;i<locsM0.length;i++){
	            Operator m1 = apsM0M1[i].value().op();
	            Operator m2 = functions[i];
	            opToOp.put(m1, m2);
	        }

	        OpReplacer opRep = new OpReplacer(opToOp);

	        Term Sn = sequentToFormula(getLast().sequent());
	        
	        Term M1M2Sn = opRep.replace(Sn);
	        
	        fpCond = tb.imp(tb.and(M1M2Sn, UM2post), Sn);
	} else {
	    throw new UnhandledCase("Special falsifiability preservation condition does not exist for branch:"+ branchType);
	}
    }

    
    
    public Boolean isValid() {
	if(form2isValid==null||!form2isValid){
	    return form2isValid; //null or false;
	}
	final Node parent = node.parent();
	if(ruleType == RuleType.LOOP_INV){
	    Node n0 = parent.child(0); //First branch,  invariant holds in the beginning
	    Node n1 = parent.child(1); //Second branch, invariant is preserved
	    return n0.isClosed() && n1.isClosed();
	}else if(ruleType == RuleType.METH_CONTR){
	    Node n0 = parent.child(0); //First branch, Contract precondition holds in the beginning
	    return n0.isClosed();
	}else{
	    throw new UnknownCalculus("Unknown rule type:"+ruleType,null);
	}
	//return false;
    }


    private Term sequentToFormula(Sequent seq){
	Semisequent semi = seq.antecedent();
	Iterator<ConstrainedFormula> it = semi.iterator();
	Term ante = tb.tt(); 
	while(it.hasNext()){
	    ante = tb.and(ante, it.next().formula());
	}
	semi = seq.succedent();
	it = semi.iterator();
	Term succ = tb.ff();
	while(it.hasNext()){
	    succ = tb.or(succ, it.next().formula());
	}
	return tb.imp(ante, succ);
    }
    
    ProofTreeAdapter getFPProofTreeListener(){
	return new FPProofTreeListener2();
    }
    
    private Node getLast() {
	return fp.branchNode;
    }
    
    /**@return true if this FP condition belongs to the branch that fp represents. 
     * Note that special falsifiability preservation conditions differ depending
     * on the last node they are constructed from. */
    public boolean belongsTo(FalsifiabilityPreservation fp){
	return getLast()==fp.branchNode;
    }
    
    public String toString(){
	String res = "Falsifiability preservation from node "+fp.branchNode.serialNr()+" to " + node.parent().serialNr();
	if(isValid()==null){
	    return res;
	}else{
	    return res += " is "+isValid();
	}
    }


    /**
     * Used to listen to side-proofs created by {@code FPCondition.check()} and
     * to update the return value of {@code FPCondition.isValid()}. If a
     * side-proof is closed, then this falsifiability preservation condition is
     * valid.
     */
    protected class FPProofTreeListener2 extends ProofTreeAdapter {
	public void proofClosed(ProofTreeEvent e) {
	    //System.out.println("form2isValid==true");
	    form2isValid = true;
	    validityUpdate();
	}
	
    }
    
    /**This listener is not used for the proof of the SFP but for the verification proof (from which the SFP was constructed)
     * We update the validity of SFP if the FIRST or SECOND branch of a contract rule closes. */
    protected class ProofTreeListener3 extends ProofTreeAdapter {
	/**This is to store the last state of the FIRST node in order to fire events
	 * only if a change occured */
	boolean n0closed=false;
	
	/**This is to store the last state of the SECOND node in order to fire events
	 * only if a change occured */
	boolean n1closed=false;
	
	/**For the case that the FIRST or SECOND branch of a contract rule has been closed. */
	public void proofGoalRemoved(ProofTreeEvent e) {
	    boolean isRelevant = false;
	    final Node parent = node.parent();
	    if (ruleType == RuleType.LOOP_INV) {
		Node n0 = parent.child(0); // First branch, invariant holds in the beginning
		Node n1 = parent.child(1); // Second branch, invariant is  preserved
		if(n0.isClosed()!=n0closed){
		    n0closed = !n0closed;
		    isRelevant = true;
		}
		if(n1.isClosed()!=n1closed){
		    n1closed = !n1closed;
		    isRelevant = true;
		}
	    } else if (ruleType == RuleType.METH_CONTR) {
		Node n0 = parent.child(0); // First branch, Contract precondition holds in the beginning
		if(n0.isClosed()!=n0closed){
		    n0closed = !n0closed;
		    isRelevant = true;
		}
	    }
	    if (isRelevant) {
		validityUpdate();
	    }
	}
    }

    


}
