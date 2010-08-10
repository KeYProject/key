// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.bugdetection;

import java.lang.reflect.InvocationTargetException;
import java.util.Iterator;
import java.util.Vector;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.bugdetection.BugDetector.MsgMgt;
import de.uka.ilkd.key.bugdetection.BugDetector.UnhandledCase;
import de.uka.ilkd.key.bugdetection.FalsifiabilityPreservation.BranchType;
import de.uka.ilkd.key.bugdetection.FalsifiabilityPreservation.RuleType;
import de.uka.ilkd.key.collection.ImmutableMapEntry;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AnonymousUpdate;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.SingleProof;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.visualdebugger.ProofStarter;

/** Falsifiability preservation condition and informations for a node
 * Instances of this class are associated with Nodes in the hashmap {@code Proof.nodeToSMTandFPData} 
 * @author gladisch */
public  class FPCondition {
    /**
     * The falsifiability preservation is considered between this node and its
     * parent node. Thus this node is the branch of the rule application in
     * focus
     */
    public final Node node;

    public final BranchType branchType;
    public final RuleType ruleType;

    /**
     * The formula to be proved in order to guarantee falsifiability
     * preservation. 
     * <p>If this can be the Special Falsifiability Preservation
     * condition (SFP) then be aware that additionally the FIRST and SECOND branches 
     * of contract rules have to be closed. Care should be taken by the method isValid(). 
     */
    public Term fpCond;

    /** the parent {@code node} */
    protected Node parent;
    /**
     * Gives access to some utilities like Services and MsgMgt
     * (MessageManagement)
     */
    protected final BugDetector bd;
    protected TermBuilder tb = TermBuilder.DF;

    /**
     * Informs if the falsifiability preservation condition is valid. Null
     * means, don't know. 
     * <p>WARNING: In the special falsifiability preservation condition this field has a different meaning,
     * it represents only formula (2) in the paper. Additionally the FIRST and SECOND branch have to be
     * proved.
     */
    private Boolean isvalid = null;
    protected Vector<FalsifiabilityPreservation> fpListeners = 
	new Vector<FalsifiabilityPreservation>();


    /**After calling the constructor also call {@code addFPListener()}, {@code constructFPC()}, {@code check()}, {@code validityUpdate}.
     * <p>Warning: this constructor has a side-effect on the Proof-object because it adds the newly created object
     * to the proof; it associates {@code node} with this object. This again triggers a notification to proofTreeListeners
     * that smtAndFPdata has been added. */
    public FPCondition(Node node, RuleType ruleType, BranchType branchType,
	    BugDetector bd) {
	this.node = node;
	this.ruleType = ruleType;
	this.branchType = branchType;
	this.bd = bd;
	parent = node.parent();
	node.addSMTandFPData(this);
//	if(FalsifiabilityPreservation.getFPCondition(node)!=this){
//	    throw new RuntimeException();
//	}
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
	if(!fpListeners.contains(fp)){
	    fpListeners.add(fp);
	}
    }
    
    /**This method is meant to be applied on the node that is the result of the application
     * of the hide_left or hide_right rules.
     * @param n the node that is the result of the rule application hide_left or hide_right.
     * @param succ if true then only the succedent is analyzed, otherwise only the antecedent is analyzed.
     * @return formulas that are contained in n.parent() but not in n. */
    protected static Vector<ConstrainedFormula> findMissingFormulas(Node n, boolean succ) {
	Vector<ConstrainedFormula> res = new Vector<ConstrainedFormula>();
	if (n == null) {
	    return res;
	}
	final Node parent = n.parent();
	Semisequent nss=null; //semisequent of n
	Semisequent pss=null; //parent semi-sequent
	if(succ){
	    pss = parent.sequent().succedent();
	    nss  = n.sequent().succedent();
	}else{
	    pss = parent.sequent().antecedent();
	    nss  = n.sequent().antecedent();
	}

	final Iterator<ConstrainedFormula> pssIt = pss.toList().iterator();
	while (pssIt.hasNext()) {
	    ConstrainedFormula cf = pssIt.next();
	    if (!nss.contains(cf)) {
		res.add(cf);
	    }
	}
	return res;
    }

    /**
     * Call this method after initialization of this object to construct and
     * further initilizse the object the falsifiability preservation condition
     */
    public void constructFPC() {
	if(ruleType == RuleType.HIDE_LEFT || ruleType == RuleType.HIDE_RIGHT){
	    	Sequent seq = node.sequent();
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
		if(ruleType == RuleType.HIDE_LEFT){
		    Vector<ConstrainedFormula> missing = findMissingFormulas(node, false);
		    if(missing.size()!=1){
			throw new RuntimeException("Cannot determine the formula that was hidden by the rule application hide_left.");
		    }
		    succ = tb.or(succ, missing.get(0).formula());
		}else{
		    Vector<ConstrainedFormula> missing = findMissingFormulas(node, true);
		    if(missing.size()!=1){
			throw new RuntimeException("Cannot determine the formula that was hidden by the rule application hide_right.");
		    }
		    succ = tb.or(succ, tb.not(missing.get(0).formula()));		    
		}
		fpCond = tb.imp(ante, succ);
	}else if (ruleType == RuleType.LOOP_INV || ruleType == RuleType.METH_CONTR) {
	    throw new UnhandledCase(
		    "Handling of contract rules is not implemented in this FPCondition. Use SFPCondition instead.");
	} else {
	    throw new UnhandledCase("constructFPC does not handle branch type:"
		    + branchType
		    + " I think that FALSE should be returned as FP-condition.");
	}
    }

 
    protected void warning(String s, int severity) {
	bd.msgMgt.warning(s, severity);
    }

    public String toString(){
	String res = "Falsifiability preservation at node " + node.serialNr();
	if(isValid()==null){
	    return res;
	}else{
	    return res += " is "+isValid();
	}
    }
    
    /**
     * Call this method to prove the falsifiability preservation condition. The
     * prove may happen either immediately or sometime later, e.g. by creating
     * an interactive proof object that the user can prove when he wants to. The
     * behavior depends on the field {@code BugDetector.fpCheckInteractive} In
     * any case this method is non-blocking. In order to query the result use
     * the method {@code isValid()}
     */
    public void check() {
	if(fpListeners.size()==0){
	    System.out.println("Warning: FPCondition has no listeners. Normally a listener is notified when the FP condition is proved.");
	}
//	if(isValid()!=null){
//	    //This case means that the FP condition has already been checked or at least created. 
//	    //There already exists a proof object for this so we don't create a new one.
//	    //!!!  However the SFP differs depending on the end-node Sn that is used  !!!!
//	    validityUpdate();
//	    return;
//	}
	if (fpCond == null) {
	    throw new RuntimeException("Call constructFPC() before calling check()");
	}
	final ConstrainedFormula cf2 = new ConstrainedFormula(fpCond);
	final Semisequent succ = Semisequent.EMPTY_SEMISEQUENT.insert(0, cf2).semisequent();
	final Sequent poSeq = Sequent.createSuccSequent(succ);

	final Proof old = node.proof();
	final Proof proof = new Proof(this.toString(), 
					poSeq, "", 
					old.env().getInitConfig().createTacletIndex(), 
					old.env().getInitConfig().createBuiltInRuleIndex(), 
					old.getServices(), 
					old.getSettings());
	// proof.setNamespaces(old.getNamespaces());
	proof.setProofEnv(old.env());
	proof.addProofTreeListener(getFPProofTreeListener());
	final ProofAggregate pa = new SingleProof(proof, "XXX");
	
	if (bd.fpCheckInteractive) {
	    Main main = Main.getInstance();
	    main.addProblem(pa);
	} else {
	    //ConstrainedFormula newCF = new ConstrainedFormula(watchpoint);
	    //seq = seq.changeFormula(newCF, pos).sequent();
	    // start side proof
	    final ProofStarter ps = new ProofStarter();
	    ps.init(pa);
	    //final ProofEnvironment proofEnvironment = createProofEnvironment(seq, proof, maxsteps, ps);
	    try {
		SwingUtilities.invokeAndWait(new Runnable() {
		    public void run() {
			System.out.println("Running FP-side-proof in background");
			ps.run(proof.env());
		    }
		});
	    } catch (InterruptedException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
	    } catch (InvocationTargetException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
	    }
	    //The following line is probably not required because the proof 
	    //has registered a FPProofTreeListener.
	    //isvalid = ps.getProof().closed();

	}

    }

    /**This method is overwritten by SFPCondition. isvalid has a different meaning there. */
    public Boolean isValid() {
	return isvalid;
    }

    /**Call ths method, when the return value of {@code isValid()} changes.
     * The listeners are added via {@code addFPCListener}*/
    public void validityUpdate(){
	for(FalsifiabilityPreservation fp:fpListeners){
	    fp.fpcUpdate(this);
	}
    }
    
    /**@return true if this FP condition belongs to the branch that fp represents. 
     * Note that FPConditions can be shared by multiple branches in contrast to
     * special falsifiability preservation conditions. */
    public boolean belongsTo(FalsifiabilityPreservation fp){
	return true;
    }
    ProofTreeAdapter getFPProofTreeListener(){
	return new FPProofTreeListener();
    }
    
    /**
     * Used to listen to side-proofs created by {@code FPCondition.check()} and
     * to update the return value of {@code FPCondition.isValid()}. If a
     * side-proof is closed, then this falsifiability preservation condition is
     * valid.
     */
    private class FPProofTreeListener extends ProofTreeAdapter {
	public void proofClosed(ProofTreeEvent e) {
	    isvalid = true;
	    validityUpdate();
	}
    }
    
    public Services getServices(){
	return node.proof().getServices();
    }

   
}
