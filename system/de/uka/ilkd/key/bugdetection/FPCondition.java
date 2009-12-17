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
public class FPCondition {
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
	if(FalsifiabilityPreservation.getFPCondition(node)!=this){
	    throw new RuntimeException();
	}

    }

    /**Call this method after the constructor.
     * An FPCondition may be shared by multiple falsifiability preservations of branches, 
     * because multiple branches may share common nodes.
     * Adding the same object multiple times is allowed because a set is implemented.*/
    public void addFPCListener(FalsifiabilityPreservation fp){
	if(fp == null){
	    throw new NullPointerException();
	}
	if(!fpListeners.contains(fp)){
	    fpListeners.add(fp);
	}
    }
    
    /**
     * Call this method after initialization of this object to construct and
     * further initilizse the object the falsifiability preservation condition
     */
    public void constructFPC() {
	final Vector<ConstrainedFormula> cfs = findNewFormulasInSucc(node);
	final ConstrainedFormula cf = pickRelevantFormula(cfs);
	if (branchType == BranchType.THRID) {
	    throw new UnhandledCase(
		    "Handling of THIRD branch is not implemented in this FPCondition. Use SFPCondition instead.");
	} else {
	    throw new UnhandledCase("constructFPC does not handle branch type:"
		    + branchType
		    + " I think that FALSE should be returned as FP-condition.");
	}
    }

    /**
     * Returns formulas that are in succedent of node {@code n} that are not
     * present in its parent node's succedent. This is a hack in order to find
     * out what formulas have been added by rule application
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

	final Iterator<ConstrainedFormula> succIt = n.sequent().succedent()
	        .toList().iterator();
	while (succIt.hasNext()) {
	    ConstrainedFormula cf = succIt.next();
	    if (pSucc == null || !pSucc.contains(cf)) {
		res.add(cf);
	    }
	}
	return res;
    }

    /**
     * If findNewFormulasInSucc returns multiple formulas, then use this method
     * to pick the formula that looks like the one to be the main prove
     * obligation (that contains e.g. the program). Warning this method uses
     * heuristics to determine the right formula
     */
    protected ConstrainedFormula pickRelevantFormula(
	    Vector<ConstrainedFormula> cfs) {
	if (cfs.size() == 1) {
	    return cfs.firstElement();
	} else if (cfs.size() == 0) {
	    return null;
	} else {
	    warning("pickRelevantFormula() uses heuristics to determine the relevant formula. This may be unsound.",
		    0);
	    int[] score = new int[cfs.size()];
	    int i = 0;
	    for (ConstrainedFormula cf : cfs) {
		Term f = cf.formula();
		Operator op = f.op();
		if (f.executableJavaBlock() != null) {
		    score[i] += 100;
		}
		if (op instanceof Modality) {
		    score[i] += 10;
		}
	    }
	    int max = 0;
	    for (int j : score) {
		if (score[j] > score[max])
		    max = j;
	    }
	    return cfs.get(score[max]);
	}
    }

    protected void warning(String s, int severity) {
	bd.msgMgt.warning(s, severity);
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
	if (fpCond == null) {
	    throw new RuntimeException("Call constructFPC() before calling check()");
	}
	if(fpListeners.size()==0){
	    System.out.println("Warning: FPCondition has no listeners. Normally a listener is notified when the FP condition is proved.");
	}
	final ConstrainedFormula cf2 = new ConstrainedFormula(fpCond);
	final Semisequent succ = Semisequent.EMPTY_SEMISEQUENT.insert(0, cf2).semisequent();
	final Sequent poSeq = Sequent.createSuccSequent(succ);

	final Proof old = node.proof();
	final Proof proof = new Proof("Falsifiability preservation at node " + node.serialNr(), 
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

}
