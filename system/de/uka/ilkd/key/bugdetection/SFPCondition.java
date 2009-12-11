package de.uka.ilkd.key.bugdetection;

import java.util.Iterator;
import java.util.Vector;

import de.uka.ilkd.key.bugdetection.BugDetector.MsgMgt;
import de.uka.ilkd.key.bugdetection.BugDetector.UnhandledCase;
import de.uka.ilkd.key.bugdetection.BugDetector.UnknownCalculus;
import de.uka.ilkd.key.bugdetection.FalsifiabilityPreservation.BranchType;
import de.uka.ilkd.key.bugdetection.FalsifiabilityPreservation.RuleType;
import de.uka.ilkd.key.collection.ImmutableMapEntry;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.AnonymousUpdate;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.Update;

public class SFPCondition extends FPCondition {
    
    /**This update is is extracted from the formula in the THIRD branch created by a contract rule.
     * This is the update that describes the state changed before the application of the contract 
     * @see extractUpdates*/
    private Update prefix;
    
    /**This update is is extracted from the formula in the THIRD branch created by a contract rule
     * This is the update that describes the state changed after the application of the contract  
     * @see extractUpdates*/
    private Update anon;
    
    private final Node last;

    public SFPCondition(Node node, Node last, RuleType ruleType, BranchType branchType,
	    MsgMgt msgMgt) {
	super(node, ruleType, branchType, msgMgt);
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
	    getContractPostCond(subsub);
	    return;
	}
	//warning("Didn't find anonymous update at the expected syntactical position. Now guessing starts", 1);
	throw new UnhandledCase("Can't determine prefix and anon updates");
    }

    /**
     * Extracts the post condition form the applied contract rule. This method
     * is called by extractUpdatesAndPost For method contract this is clear; -
     * For loop invariant the expected structure is INV->[b=cond](b=false->phi).
     * From this we extract (INV & [b=cond]b=false)
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
	    TermFactory tf = new TermFactory();
	    XXX
	    
//		PosTacletApp tacletApp = (PosTacletApp) parent.getAppliedRuleApp();
//		SVInstantiations svInst = tacletApp.instantiations();
//		Iterator<ImmutableMapEntry<SchemaVariable, InstantiationEntry>> entryIt = svInst
//		        .pairIterator();
//		while (entryIt.hasNext()) {
//		    System.out.println(entryIt.next());
//		}

		return null;	    
	}else if (ruleType != RuleType.METH_CONTR) {
	    throw new UnhandledCase("Extraction of method contract post condition is not implemented yet.");
	}
	throw new UnhandledCase("Unknown ruleType:"+ruleType);
    }

}
