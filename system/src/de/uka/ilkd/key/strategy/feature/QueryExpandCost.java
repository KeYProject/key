package de.uka.ilkd.key.strategy.feature;

import java.math.BigInteger;
import java.util.Iterator;
import java.util.WeakHashMap;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.rule.QueryExpand;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

/**
 * A Feature that computes the cost for using the query expand rule. 
 * @author gladisch
 */
public class QueryExpandCost implements Feature {
	
	/** Constant that represents the boolean value true */
    public static final RuleAppCost ZERO_COST = LongRuleAppCost.ZERO_COST;
    /** Constant that represents the boolean value false */
    public static final RuleAppCost TOP_COST  = TopRuleAppCost.INSTANCE;
    
    public final boolean preventRepetitionAtSamePos;
    public final boolean computeCostFromIntLiterals;
    public final boolean computeCostFromTermSize;
    public final boolean computeCostFromOuterTerm;

    public QueryExpandCost(boolean preventRepetitionAtSamePos, 
    		               boolean computeCostFromIntLiterals,
    		               boolean computeCostFromTermSize,
    		               boolean computeCostFromOuterTerm){
		super();
		this.preventRepetitionAtSamePos = preventRepetitionAtSamePos;
		this.computeCostFromIntLiterals = computeCostFromIntLiterals;
		this.computeCostFromTermSize    = computeCostFromTermSize;
		this.computeCostFromOuterTerm   = computeCostFromOuterTerm;
	}
    
	@Override
	public RuleAppCost compute(RuleApp app, PosInOccurrence pos, Goal goal) {
		final Services services = goal.proof().getServices();
		final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
		final Term t = pos.subTerm();

		// System.out.print("G:"+goal.hashCode()+"   ");
		int cost=200; 
	
	
		
		//if(computeCostFromIntLiterals){
			// System.out.print("literal sum: "+literalsInArgumentsToCost(t,integerLDT,services));
	//    int litcost = literalsInArgumentsToCost(t,integerLDT,services)*50; //If the factor is too small, then higher cost has no effect for some reason.
	//		if(!isStepCaseBranch(goal)){
	//			cost += litcost;
	//		}
			/*else{
				//cost -= litcost;
				if(!pos.isInAntec()){
					cost = 100;
				}
			}
			*/
			/*if(litCost != 0){
			// System.out.println("LiteralToCost:"+litCost + "  final cost:"+cost);
			return LongRuleAppCost.create(cost);
			}
			 */
		//}
			
		if(preventRepetitionAtSamePos ){
				int count = queryExpandAlreadyAppliedAtPos(app,pos,goal);
				if(count>1){
					return TOP_COST;
				}else{
					cost += count*2000;
				}
		}
/*			
		if(computeCostFromTermSize){
			int depth = t.depth();
			int depthcost = (depth*(depth+10)*5)-100;
			
			// System.out.print("  query term depth: "+t.depth());
			cost += depthcost;   //Subtract 100 because t.depth() is usually greater than 2. 
		}
*/
/*		
		if(computeCostFromOuterTerm){
			PosInOccurrence posUp=pos.up();
			int depth=0;
			Term posChild = t;
			Term upTerm=null;
			//Compute the depth of the outer term.
			while(posUp!=null && posUp.subTerm().sort()!=Sort.FORMULA){
				 upTerm= posUp.subTerm();
				 for(int i=0;i<upTerm.arity();i++){
					 Term sub=upTerm.sub(i);
					 if(sub==posChild) continue; //skip the term that leads to the query in focus of the rule application.
					 depth=Math.max(depth, sub.depth());
				 }
				 depth++;
				 posChild=upTerm;
				 posUp=posUp.up();
			}

			// System.out.print("  outer depth: "+depth);
			cost += depth*(depth+10)*5;
		}
*/
		String tStr = t.toString(); int maxLen = tStr.length()>50?50:tStr.length();
		System.out.println("  cost="+cost + "    query:.."+tStr.substring(15, maxLen-1)+"..");

		return LongRuleAppCost.create(cost);
	}

	/**
	 * @param t the query that is considered for the rule expand query.
	 * @param iLDT
	 * @param serv
	 * @return Cost that is computed base on the integer literals occurring in the numerical arguments of the query t.
	 * @see <code>literalsToCost</code>
	 */
	private static int literalsInArgumentsToCost(Term t, IntegerLDT iLDT, Services serv){
		final Namespace sorts = serv.getNamespaces().sorts();
		final Sort intSort = (Sort) sorts.lookup(IntegerLDT.NAME);
		int cost=0;
		//The computation is limited to arguments that have an arithmetic type. E.g., don't calculate int literals in the heap parameter. 
		for(int i=0;i<t.arity();i++){  
			Term arg = t.sub(i);
			if(arg.sort()==intSort){
				cost += literalsToCost(arg, iLDT, serv);
			}
		}
		return cost;
	}
	
	/** Absolute values of literal occurring in t a used for cost computation.
	 *  The cost of literals is sorted the following way:0,1,-1,2,-2,3,-3,...
     * @param t The term is expected to be an argument of the query.
     * @param iLDT
     * @param serv
     * @return Sum* of the absolute values of integer literals occurring in t multiplied by two. 
              (*) The sum is modified by extrapolating negative numbers from zero by one. The
                  cost of a query f(n-1) a slightly higher cost than the cost of f(n+1).
     */
	private static int literalsToCost(Term t, IntegerLDT iLDT, Services serv){
		//if(t.op() instanceof Function && iLDT.hasLiteralFunction((Function)t.op())){
		if(t.op() == iLDT.getNumberSymbol()){
			String strVal = AbstractTermTransformer.convertToDecimalString(t, serv);
			int val =Integer.parseInt(strVal);
			if(val>=0){
				return val*2;
			}else{
				return (val*-2)+1; //Negative numbers get a slightly higher cost than positive numbers.
			}
		}else{
			int sum=0;
			for(int i=0;i<t.arity();i++){
				sum  += literalsToCost(t.sub(i), iLDT, serv);
			}
			return sum;
		}
	}

	private static Term findLiteral(Term t, IntegerLDT iLDT){
		//if(t.op() instanceof Function && iLDT.hasLiteralFunction((Function)t.op())){
		if(t.op() == iLDT.getNumberSymbol()){
			return t;
		}else{
			for(int i=0;i<t.arity();i++){
				Term tmp = findLiteral(t.sub(i), iLDT);
				if(tmp!=null){
					return tmp;
				}
			}
		}
		return null;
	}
	
	/** The method checks if the same rule has been applied earlier on this branch
	 *  at the same position in the sequent. This method detects repetitive rule
	 *  applications and is used to prevent loops in the proof tree.
	 */
	protected static int queryExpandAlreadyAppliedAtPos(RuleApp app, PosInOccurrence pos, Goal goal){
		 int count=0;
		 ImmutableList<RuleApp> l =goal.appliedRuleApps();
	        if(l!=null && !l.isEmpty()){
	        	Iterator<RuleApp> i=l.iterator();
	        	while(i.hasNext()){
	        		RuleApp ra = i.next();
	        		SequentFormula racf = ra.posInOccurrence().constrainedFormula();
	        		SequentFormula curcf = pos.constrainedFormula();
	        		Term raterm = ra.posInOccurrence().subTerm();
	        		Term curterm = pos.subTerm();
	        		//if(ra.posInOccurrence().eqEquals(pos) && ra.rule()==QueryExpand.INSTANCE){
	        		if(raterm.equals(curterm)){
	        			 System.out.println("Rule already applied:"+app.rule().displayName()+ " on "+raterm.toString());
	        			count++;
	        			if(count>2) break;
	        		}
	        	}
	        }
	     return count;
	}
	
	protected static boolean isStepCaseBranch(Goal goal){
		Node node = goal.node();
		while(node!=null){
			NodeInfo ni = node.getNodeInfo();
			if(ni!=null && ni.getBranchLabel()!=null){
				String branchName = ni.getBranchLabel().toLowerCase();
				if(branchName.indexOf("step case")>=0 || branchName.indexOf("body preserves")>=0){
					System.out.println("Step Case found!");
					return true;
				}else if(branchName.indexOf("base case")>=0 || 
						branchName.indexOf("invariant initially")>=0 ||
						branchName.indexOf("use case")>=0 ){
					//System.out.println("Base Case found!");
					return false;
				}
			}
			node=node.parent();
		}
		return false;
	}

}

