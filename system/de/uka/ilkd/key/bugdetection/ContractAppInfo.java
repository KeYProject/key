package de.uka.ilkd.key.bugdetection;

import java.util.Iterator;
import java.util.Vector;

import de.uka.ilkd.key.bugdetection.BugDetector.UnhandledCase;
import de.uka.ilkd.key.bugdetection.BugDetector.UnknownCalculus;
import de.uka.ilkd.key.bugdetection.FalsifiabilityPreservation.RuleType;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.updatesimplifier.Update;


/**A tuple for collecting data about contract rule application 
 * @see constructFPC
 * @author gladisch*/
public class ContractAppInfo{
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
    
    public String toString(){
	return "PREFIX:"+prefix + "\nANON:"+anon + "\nContractPost:"+contractPost;
    }

    /**
     * Returns formulas that are in succedent of node {@code n} that are not
     * present in its parent node's succedent. This is a hack in order to find
     * out what formulas have been added by rule application
     * 
     * @author gladisch
     */
    protected static Vector<ConstrainedFormula> findNewFormulasInSucc(Node n) {
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
    protected static ConstrainedFormula pickRelevantFormula(
	    Vector<ConstrainedFormula> cfs) {
	if (cfs.size() == 1) {
	    return cfs.firstElement();
	} else if (cfs.size() == 0) {
	    return null;
	} else {
	    BugDetector.DEFAULT.msgMgt.warning("pickRelevantFormula() uses heuristics to determine the relevant formula. This may be unsound.",
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

    public static class  LoopInvAppInfo extends ContractAppInfo{
    	    
	protected TermBuilder tb = TermBuilder.DF;
	
	public static LoopInvAppInfo getContractAppInfo(Node n){
	    return new LoopInvAppInfo(n);
	}

    	    /**This class extracts information from a contract rule application.
    	     * @param node must be the THIRD child node created by the loop invariant rule or method contract 
    	     * rule app from which information will be extracted */
    	    private LoopInvAppInfo(Node node){
    		final Vector<ConstrainedFormula> cfs = findNewFormulasInSucc(node);
    		final ConstrainedFormula cf = pickRelevantFormula(cfs);
    		extractUpdatesAndPost(cf.formula());
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
    		//if(ruleType==RuleType.LOOP_INV){
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
//    		}else if (ruleType != RuleType.METH_CONTR) {
//    		    throw new UnhandledCase("Extraction of method contract post condition is not implemented yet.");
//    		}
//    		throw new UnhandledCase("Unknown ruleType:"+ruleType);
    	    }
    
        }
    
    public static class MethContrAppInfo extends ContractAppInfo{
	
	public static ContractAppInfo getContractAppInfo(Node n){
	    return n.parent().getNodeInfo().cInfo;
	}
    }

}