// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy.feature;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
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
    
    /** If the literals in a query become greater than abs(ConsideredAsBigLiteral), then
     *  this is interpreted as a "loop smell", i.e. the proof construction is in a loop
     *  and produces big literals.*/
    public static final int ConsideredAsBigLiteral = 7;
    
    private final int baseCost; 
    private final int maxRepetitionsOnSameTerm;
    private final int termAgeFactor;
    private final boolean useExperimentalHeuristics;
    
    /**
     * @param baseCost Should be set to 200. This was the cost before this class was introduced.
     * @param maxRepetitionsOnSameTerm Search in the current branch if query expand 
     *       has been already applied on this term. For each such application a penalty cost is added. 
     *        If this limit is exceeded the cost is set to TOP_COST, i.e. the rule is not applied. 
     * @param termAgeFactor This factor (must be >=0) sets the cost of older queries lower, than that
     *       of younger queries (i.e. that occur later in proofs). The effect is a breath-first search
     *       on the expansion of queries.
     *       In class <code>QueryExpand</code> the time is stored, when queries can be
     *       expanded for the first time. 
     * @param useExperimentalHeuristics Activates experimental, pattern-based heuristics.
     */
    public QueryExpandCost(int baseCost, 
    		               int maxRepetitionsOnSameTerm,
    		               int termAgeFactor,
    		               boolean useExperimentalHeuristics){
		super();
		this.baseCost=baseCost;
		this.maxRepetitionsOnSameTerm=maxRepetitionsOnSameTerm;
		this.termAgeFactor=termAgeFactor;
		this.useExperimentalHeuristics=useExperimentalHeuristics;
	}
    
	@Override
	public RuleAppCost compute(RuleApp app, PosInOccurrence pos, Goal goal) {
		final Services services = goal.proof().getServices();
		final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
		final Term t = pos.subTerm();

		// System.out.print("G:"+goal.hashCode()+"   ");
		long cost=baseCost; 
	
	
		
		if(useExperimentalHeuristics){
			// System.out.print("literal sum: "+literalsInArgumentsToCost(t,integerLDT,services));
			int litcost = maxIntliteralInArgumentsTimesTwo(t,integerLDT,services); //If the factor is too small, then higher cost has no effect for some reason.
			if(litcost>ConsideredAsBigLiteral*2){
				return TOP_COST;
			}
			//cost += litcost;
		}
			
		if(maxRepetitionsOnSameTerm!=-1 && maxRepetitionsOnSameTerm<Integer.MAX_VALUE){
				int count = queryExpandAlreadyAppliedAtPos(app,pos,goal);
				if(count>maxRepetitionsOnSameTerm){
					return TOP_COST;
				}else{
					cost += count*2000l;
				}
		}
		
		if(termAgeFactor>0){
			Long qtime = QueryExpand.INSTANCE.getTimeOfQuery(t);
			if(qtime!=null){
					cost += qtime * (long)termAgeFactor;
			}else{
				System.err.println("QueryExpandCost::compute. Time of query should have been set already. The query was:"+t);
			}
		}

		//String tStr = t.toString(); int maxLen = tStr.length()>50?50:tStr.length();
		//System.out.println("  cost="+cost + "    query:.."+tStr.substring(15, maxLen-1)+"..");

		return LongRuleAppCost.create(cost);
	}

	/**
	 * @param t the query that is considered for the rule expand query.
	 * @param iLDT
	 * @param serv
	 * @return Cost that is computed base on the integer literals occurring in the numerical arguments of the query t.
	 * @see <code>literalsToCost</code>
	 */
	private static int maxIntliteralInArgumentsTimesTwo(Term t, IntegerLDT iLDT, Services serv){
		final Namespace sorts = serv.getNamespaces().sorts();
		final Sort intSort = (Sort) sorts.lookup(IntegerLDT.NAME);
		int cost=0;
		//The computation is limited to arguments that have an arithmetic type. E.g., don't calculate int literals in the heap parameter. 
		for(int i=0;i<t.arity();i++){  
			Term arg = t.sub(i);
			if(arg.sort()==intSort){
				cost = Math.max(cost, sumOfAbsLiteralsTimesTwo(arg, iLDT, serv));
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
	private static int sumOfAbsLiteralsTimesTwo(Term t, IntegerLDT iLDT, Services serv){
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
				sum  += sumOfAbsLiteralsTimesTwo(t.sub(i), iLDT, serv);
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
	protected int queryExpandAlreadyAppliedAtPos(RuleApp app, PosInOccurrence pos, Goal goal){
		 int count=0;
		 ImmutableList<RuleApp> appliedRuleApps =goal.appliedRuleApps();
	        if(appliedRuleApps!=null && !appliedRuleApps.isEmpty()){
	        	Iterator<RuleApp> appliedRuleAppIter=appliedRuleApps.iterator();
	        	while(appliedRuleAppIter.hasNext()){
	        		RuleApp appliedRuleApp = appliedRuleAppIter.next();
	        		final PosInOccurrence pio = appliedRuleApp.posInOccurrence();
	        		if(pio!=null){
		        		Term oldterm = pio.subTerm();
		        		Term curterm = pos.subTerm();
		        		if(appliedRuleApp.rule().equals(QueryExpand.INSTANCE) && 
		        				oldterm.equals(curterm)){
		        			count++;
		        			if(count>maxRepetitionsOnSameTerm) break;
		        		}
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
					//System.out.println("Step Case found!");
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

	private static int computeCostFromTermSize(Term t){
		int depth = t.depth();
		int depthcost = (depth*(depth+10)*5)-100;
		
		// System.out.print("  query term depth: "+t.depth());
		return depthcost;   //Subtract 100 because t.depth() is usually greater than 2. 		
	}
	
	private static int computeCostFromOuterTerm(PosInOccurrence pos){
		PosInOccurrence posUp=pos.up();
		final Term t = pos.subTerm();
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
		return depth*(depth+10)*5;
	}

	public int getMaxRepetitionsOnSameTerm(){
		return maxRepetitionsOnSameTerm;
	}
}