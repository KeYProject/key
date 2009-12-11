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

public class SFPCondition extends FPCondition {
    
    /**This update is is extracted from the formula in the THIRD branch created by a contract rule.
     * This is the update that describes the state changed before the application of the contract 
     * @see extractUpdates*/
    private Update prefix;
    
    /**This update is is extracted from the formula in the THIRD branch created by a contract rule
     * This is the update that describes the state changed after the application of the contract  
     * @see extractUpdates*/
    private Update anon;
    
    /**Post condition of the contract that was applied at {@code parent}. 
     * This field is initialized by {@code extractUpdatesAndPost()}*/
    private Term contractPost;
    
    private final Node last;

    public SFPCondition(Node node, Node last, RuleType ruleType, BranchType branchType,
	    BugDetector bd) {
	super(node, ruleType, branchType, bd);
	this.last = last;
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
	    extractUpdatesAndPost(cf.formula());
	    assert prefix!=null; 
	    assert anon!=null;
	    assert contractPost != null;
	    final Location[] locsM0 = new Location[anon.locationCount()];
	    final AssignmentPair[] apsM0M1 = new AssignmentPair[anon.locationCount()];
	    final LocationDescriptor[] locDescM0 = new LocationDescriptor[locsM0.length];
	    for(int i =0;i<locsM0.length;i++){
		locsM0[i] = anon.location(i);
		apsM0M1[i] = anon.getAssignmentPair(i);
		locDescM0[i] = new BasicLocationDescriptor(apsM0M1[i].locationAsTerm());
	    }
	    
	        UpdateFactory uf = new UpdateFactory(bd.services, new UpdateSimplifier());
	        AnonymisingUpdateFactory auf = new AnonymisingUpdateFactory(uf);
	        
	        RigidFunction[] functions = auf.createUninterpretedFunctions(locDescM0, bd.services);
	        
	        Term M2post = auf.createAnonymisingUpdateTerm ( locDescM0, functions, contractPost, bd.services );
	        Term UM2post = uf.apply(prefix, M2post);
	        
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
	        
	        Main main = Main.getInstance();
	        KeYMediator mediator = main.mediator();
	        
	        Proof old = node.proof();
//	        Proof p = new Proof() ;
//	        mark(old.root());
//
//	        p.setProofEnv(old.env());
//	        mainFrame.addProblem(new SingleProof(p, "XXX"));
//	        changeWish = n;
	        
	        ConstrainedFormula cf2 = new ConstrainedFormula(fpCond);
		Semisequent succ = Semisequent.EMPTY_SEMISEQUENT.insert(0,cf2).semisequent();
		Sequent poSeq = Sequent.createSuccSequent(succ);
			        
		//Proof proof = new Proof("A Hand-made proof", bd.services);
		Proof proof = new Proof("sdf", poSeq, "",
				mediator.getProof().env().getInitConfig().createTacletIndex(), 
				mediator.getProof().env().getInitConfig().createBuiltInRuleIndex(),
				bd.services,
				old.getSettings()); 
		//proof.setNamespaces(old.getNamespaces());
		proof.setProofEnv(old.env());

//		Sequent seq = poSeq;
//		Node rootNode = new Node(proof,seq);
//		proof.setRoot(rootNode);
	        main.addProblem(new SingleProof(proof, "XXX"));

		//Goal firstGoal = new Goal(rootNode, proof.env().buildRuleAppIndex());
		//proof.add(firstGoal);
		/* In order to apply rules, the Namespaces need to be in place.*/

//	        WatchpointPO po = new WatchpointPO("XXXX", poSeq);
//		    //ProofOblInput po = poBrowser.getAndClearPO();
//		    if(po != null) {
//			ProblemInitializer pi = new ProblemInitializer(main);
//			try {
//			    pi.startProver(mediator.getProof().env(), po);
//			} catch(ProofInputException e)  {
//			    throw new RuntimeException(e);
//			}
//		    }

//     	   	ProblemInitializer init = new ProblemInitializer(main);
//    	    ProofEnvironment env = mediator.getSelectedProof().env();
//            prob.setInitConfig(env.getInitConfig());
//	    ProblemInitializer pi = new ProblemInitializer(Main.getInstance());
//	    pi.startProver(env, prob);


	        
//	        //return auf.createAnonymisingUpdateTerm(locations, targetTerm, services);
//
//	        for(Term t : actualParams) {
//	            ProgramVariable pv = (ProgramVariable) t.op();
//	            modifies = modifies.add(new BasicLocationDescriptor(TB.var(pv)));
//	        }
//
//	        LocationDescriptor[] locationsArray = locations.toArray(new LocationDescriptor[locations.size()]);
//	        RigidFunction[] functions = createUninterpretedFunctions(locationsArray,
//	        	bd.services);
//	        return createAnonymisingUpdateTerm ( locationsArray, functions,
//	                                             targetTerm, bd.services );
	    
	} else {
	    throw new UnhandledCase("Special falsifiability preservation condition does not exist for branch:"+ branchType);
	}
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
	    
//		PosTacletApp tacletApp = (PosTacletApp) parent.getAppliedRuleApp();
//		SVInstantiations svInst = tacletApp.instantiations();
//		Iterator<ImmutableMapEntry<SchemaVariable, InstantiationEntry>> entryIt = svInst
//		        .pairIterator();
//		while (entryIt.hasNext()) {
//		    System.out.println(entryIt.next());
//		}

	    return res;	    
	}else if (ruleType != RuleType.METH_CONTR) {
	    throw new UnhandledCase("Extraction of method contract post condition is not implemented yet.");
	}
	throw new UnhandledCase("Unknown ruleType:"+ruleType);
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
}
