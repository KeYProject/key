package de.uka.ilkd.key.bugdetection;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Vector;

import de.uka.ilkd.key.bugdetection.BugDetector.MsgMgt;
import de.uka.ilkd.key.bugdetection.BugDetector.UnhandledCase;
import de.uka.ilkd.key.bugdetection.BugDetector.UnknownCalculus;
import de.uka.ilkd.key.bugdetection.FalsifiabilityPreservation.BranchType;
import de.uka.ilkd.key.bugdetection.FalsifiabilityPreservation.RuleType;
import de.uka.ilkd.key.collection.ImmutableMapEntry;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.AnonymisingUpdateFactory;
import de.uka.ilkd.key.logic.BasicLocationDescriptor;
import de.uka.ilkd.key.logic.ConstrainedFormula;
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
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.visualdebugger.watchpoints.WatchPoint;
import de.uka.ilkd.key.visualdebugger.watchpoints.WatchpointPO;

/**Special Falsifiability Preservation Condition as described in the paper
 * <br> 
 * Christoph Gladisch. Could we have chosen a better Loop Invariant or Method Contract? In Proc. TAP 2009
 * <br>
 * Instances of this class are associated with Nodes in the hashmap {@code Proof.nodeToSMTandFPData}
 * @author gladisch */
public class SFPCondition extends FPCondition {
    
    
    private final Node last;
    
    /**Formula 2 according to the paper. The SFP formula. The condition if the FIRST and SECOND branches
     * of the contract rule are closed is not expressed here. */
    private Boolean form2isValid=null;

    /**After calling the constructor also call {@code addFPListener()}, {@code constructFPC()}, {@code check()}, {@code validityUpdate}.
     * <p>Warning: this constructor has a side-effect on the Proof-object because it adds the newly created object
     * to the proof; it associates {@code node} with this object. This again triggers a notification to proofTreeListeners
     * that smtAndFPdata has been added. */
    public SFPCondition(Node node, Node last, RuleType ruleType, BranchType branchType,
	    BugDetector bd) {
	super(node, ruleType, branchType, bd);
	this.last = last;
	node.proof().addProofTreeListener(new ProofTreeListener3());
    }
    
    /**
     * Call this method after initialization of this object to construct and
     * further initilizse the object the special falsifiability preservation condition
     */
    public void constructFPC() {
	final Vector<ConstrainedFormula> cfs = findNewFormulasInSucc(node);
	final ConstrainedFormula cf = pickRelevantFormula(cfs);
	if (branchType == BranchType.THRID) {
	    if (ruleType == RuleType.METH_CONTR) {
		warning("This was programmed for the loop invariant rule. Method contracts may or may not work correctly.",0);
	    }
	    ContractAppInfo cInfo = new ContractAppInfo(cf.formula(),ruleType);
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

	        Term Sn = sequentToFormula(last.sequent());
	        
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

    /**A tuple for collecting data about contract rule application 
     * @see constructFPC
     * @author gladisch*/
    private class ContractAppInfo{
	    /**This update is is extracted from the formula in the THIRD branch created by a contract rule.
	     * This is the update that describes the state changed before the application of the contract 
	     * @see extractUpdates*/
	    public Update prefix;
	    
	    /**This update is is extracted from the formula in the THIRD branch created by a contract rule
	     * This is the update that describes the state changed after the application of the contract  
	     * @see extractUpdates*/
	    public Update anon;
	    
	    /**Post condition of the contract that was applied at {@code parent}. 
	     * This field is initialized by {@code extractUpdatesAndPost()}*/
	    public Term contractPost;
	    
	    private RuleType ruleType;
	    
	    /**This class extracts information from a contract rule application.
	     * @param the formula (of the THIRD branch) created by the contract rule app */
	    public ContractAppInfo(Term t, RuleType ruleType){
		this.ruleType = ruleType;
		extractUpdatesAndPost(t);
	    }
	    
	    /**
	     * Looks at the top-level operator and one operator below the top-level for
	     * anonymous updates. This is where the prefix and anonymous update create in the THIRD
	     * branch of contract rules are expected. Warning: this works only with the
	     * current form of contract rules (10.12.2009)
	     */
	    private void extractUpdatesAndPost(Term t) {
		if (t.op() instanceof IUpdateOperator) {
		    prefix = Update.createUpdate(t);
		} 
		Term sub = t.sub(t.arity()-1);
		if (sub.op() instanceof IUpdateOperator) {
		    // This is the case where the anonymous update is expected.
		    //The expected form of t is: {upd}{anon}phi
		    anon = Update.createUpdate(sub);
		}
		if(prefix!=null && anon !=null){
		    Term subsub = sub.sub(sub.arity()-1);
		    //subsub is below the anonymous update
		    contractPost = getContractPostCond(subsub);
		    return;
		}
		//warning("Didn't find anonymous update at the expected syntactical position. Now guessing starts", 1);
		throw new UnhandledCase("Can't determine prefix and anon updates");
	    }

	    
	    /**
	     * Extracts the post condition form the applied contract rule. This method
	     * is called by extractUpdatesAndPost For method contract this is clear; -
	     * For loop invariant the expected structure is INV->[b=cond](b=false->phi).
	     * From this we extract (INV & [b=cond]b=false). The result is stored
	     * as a side-effect on the field {@code contractPost}
	     * */
	    private Term getContractPostCond(Term f) {
		if(ruleType==RuleType.LOOP_INV){
		    //First, extract all subformulas etc from f and check if f has the expected form
		    if(f.op()!=Op.IMP){
			throw new UnknownCalculus("Expected implication as top level op.",f);
		    }
		    final Term inv = f.sub(0);
		    final Term rightT = f.sub(1); // should represent [b=cond](b=false->phi)
		    if(!(rightT.op() instanceof Modality)){
			throw new UnknownCalculus("Expected modal operator as top level op.",rightT);
		    }
		    Modality guardMod = (Modality)rightT.op(); //should represent [..]
		    JavaBlock guardStmt = rightT.javaBlock();
		    final Term right2T = rightT.sub(0); //should represent  (b=false->phi)
		    if(right2T.op()!=Op.IMP){
			throw new UnknownCalculus("Expected implication as top level op.",f);		
		    }
		    final Term bIsFalse = right2T.sub(0);//should represent  (b=false)
		    
		    //Second, Construct now the post condition of the contract from the extracted informations
		    Term res = tb.and(inv, tb.prog(guardMod, guardStmt, bIsFalse));
		    
//			PosTacletApp tacletApp = (PosTacletApp) parent.getAppliedRuleApp();
//			SVInstantiations svInst = tacletApp.instantiations();
//			Iterator<ImmutableMapEntry<SchemaVariable, InstantiationEntry>> entryIt = svInst
//			        .pairIterator();
//			while (entryIt.hasNext()) {
//			    System.out.println(entryIt.next());
//			}

		    return res;	    
		}else if (ruleType != RuleType.METH_CONTR) {
		    throw new UnhandledCase("Extraction of method contract post condition is not implemented yet.");
		}
		throw new UnhandledCase("Unknown ruleType:"+ruleType);
	    }

    }

}
