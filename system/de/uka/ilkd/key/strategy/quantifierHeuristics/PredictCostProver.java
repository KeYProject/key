// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                Universitaet Koblenz-Landau, Germany
//                Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.SetAsListOfTerm;
import de.uka.ilkd.key.logic.SetOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * TODO: rewrite, this seems pretty inefficient ...
 */
class PredictCostProver {

	private final static TermBuilder tb = TermBuilder.DF;

	private final static Term trueT = tb.tt(), falseT = tb.ff();

	/**assume that all literal in <code>assertLiterals</code> are true*/
	private SetOfTerm assertLiterals = SetAsListOfTerm.EMPTY_SET;

	/**clauses from <code>instance</code> of CNF*/
	private Set<Clause> clauses = new HashSet<Clause>();

	private Services services;

	private PredictCostProver(Term instance, SetOfTerm assertList, 
                Services services) {
		this.assertLiterals = this.assertLiterals.union(assertList);
		this.services = services;
                initClauses(instance);
	}

	public static long computerInstanceCost(Substitution sub,
	        Term matrix,
	        SetOfTerm assertList, Services services) {
        
        
		final PredictCostProver prover = 
			new PredictCostProver ( sub.applyWithoutCasts(matrix), 
			        assertList, services );
		return prover.cost();
	}

	//init context 
	private void initClauses(Term instance) {
		IteratorOfTerm it = TriggerUtils.iteratorByOperator(instance, Op.AND);
		while (it.hasNext()) {
			SetOfTerm literals = TriggerUtils.setByOperator(it.next(),Op.OR);
			//clauses.add(new Clause(literals));
			Iterator<SetOfTerm> lit = createClause(literals.toArray(), 0).iterator();
			while (lit.hasNext()) {
			  clauses.add(new Clause(lit.next()));
			}
		}
	}

	private Set<SetOfTerm> createClause(Term[] terms, int i) {
		Set<SetOfTerm> res = new HashSet<SetOfTerm>();
		if (i >= terms.length)
			return res;
		Term self = terms[i];
		boolean ifthen = terms[i].op() == Op.IF_EX_THEN_ELSE;
		Set<SetOfTerm> next = createClause(terms, i+1);
		if(next.size()==0){
		     if(ifthen){res.add(SetAsListOfTerm.EMPTY_SET
				.add(tb.not(self.sub(0))).add(self.sub(1)));
		                 res.add(SetAsListOfTerm.EMPTY_SET
                                .add(self.sub(0)).add(self.sub(2)));
		     }
		     else res.add(SetAsListOfTerm.EMPTY_SET.add(self));
		}
		else {
			Iterator<SetOfTerm>  it = next.iterator();
			while (it.hasNext()) {
				SetOfTerm ts = it.next();
				if (ifthen) {
					res.add(ts.add(tb.not(self.sub(0)))
							    .add(self.sub(1)));
					res.add(ts.add(self.sub(0))
							.add(self.sub(2)));
				}
				else {
					res.add(ts.add(self));
				}
			}
		}
		return res;
	}

	//end 
	
    
    
	//rules of thie sub prover
	//(1) cache rule
	/**
	 * Find in the cache wether this <code>problem</code> has 
	 * ever been proved
	 */
	private Term provedFromCache(Term problem, Map cache) {
		boolean positive = true;
        Term pro = problem;
        Operator op = pro.op ();
        while ( op == Op.NOT ) {
            pro = pro.sub ( 0 );
            op = pro.op ();
            positive = !positive;
        }
        Term res = (Term)cache.get ( pro );
        if ( res != null ) return positive ? res : tb.not ( res );
        return problem;
	}
    
	/**
	 * add the problem with its result(res) to cache. if the problem is 
	 * not an atom, add its subterm with according changed res to cache.
	 */
	private void addToCache(Term problem, Term res, Map<Term, Term> cache){
		boolean temp =true;
		Term pro = problem;
		Operator op = pro.op();
		while(op==Op.NOT){
			pro = pro.sub(0);
			op = pro.op();
			temp=!temp;
		}
		cache.put(pro, temp ? res : tb.not(res));
	}
    
	//(2)self-proved rule
	/**
	 * If the given <code>problem</code>'s operation is equal,or mathmetic
	 * operation(=,>=, <=), this method will try to prove it by finding the
	 * relation between its two subterms.
	 */
	private Term provedBySelf(Term problem) {
		boolean temp = true;
		Term pro = problem;
		Operator op = pro.op();
		if (op == Op.NOT) {
			temp = !temp;
			pro = pro.sub(0);
			op = pro.op();
		}
		if (op == Op.EQUALS && pro.sub(0).equals(pro.sub(1)))
			return temp ? trueT : falseT;
		Term arithRes = HandleArith.provedByArith(pro, services);
		if(TriggerUtils.isTrueOrFalse(arithRes))
			return temp ? arithRes : tb.not(arithRes);
		else return problem;
	}

	//(3)equal rule
	/***
	 * @return trueT if problem is equal axiom, false if problem's negation
	 * is equal axiom. Otherwise retrun problem.  
	 */
	private Term provedByequal(Term problem, Term axiom) {
		boolean temp = true;
		Term pro = problem;
		if (pro.op() == Op.NOT) {
			pro = pro.sub(0);
			temp = !temp;
		}
		Term ax = axiom;
		if (ax.op() == Op.NOT) {
			ax = ax.sub(0);
			temp = !temp;
		}
		if (pro.equals(ax))
			return temp ? trueT : falseT;
		return problem;
	}  
	
	//(4)combine provedByequal and provedByArith .
	/** 
	 * @param problem
	 * @param axiom
	 * @return if axiom conduct problem then return trueT. If axiom conduct
	 *         negation of problem return fastT. Otherwise, return problem
	 */
	private Term provedByAnother(Term problem, Term axiom) {
		Term res = provedByequal(problem,axiom);
		if(TriggerUtils.isTrueOrFalse(res))return res;
		return HandleArith.provedByArith(problem, axiom, services);
	}

    
	//(5) combine rules
	/**
	 * try to prove <code>problem</code> by know <code>assertLits</code>
	 * 
	 * @param problem  a literal
	 *            to be proved
	 * @param assertLits a set of term
	 *            assertLiterals in which all literals are true
	 * @return return <code>trueT</code> if if formu is proved to true,
	 *         <code> falseT</code> if false, and <code>atom</code> if it
	 *         cann't be proved.
	 */
	private Term proveLiteral(Term problem, SetOfTerm assertLits) {
		Term res;
/*		res = provedFromCache(problem, cache);
		if (res.equals(trueT) || res.equals(falseT)) {
			return res;
		} */
		res = provedBySelf(problem);
		if (TriggerUtils.isTrueOrFalse ( res )) {
//			addToCache(problem,res,cache);
			return res;
		}
		final IteratorOfTerm it = assertLits.iterator();
		while (it.hasNext()) {
			Term t = it.next();
			res = provedByAnother(problem, t);
			if (TriggerUtils.isTrueOrFalse ( res )) {
//				addToCache(problem, res,cache);
				return res;
			}
		}
		return problem;
	}

	//end
    
        
	//cost computation
    	/**do two step refinement and return the cost */
	private long cost() {
		return firstRefine();
	}

	/**refine every clause, by assume assertList are true and
	 * if a clause's cost is 0 which means it is refined to false, then
	 * cost 0 returned. If every clause's cost is -1 which means every clause
	 * is refined to true, cost -1 returned. Otherwise, multiply of every 
	 * cost is return. Beside, if a clause is refined to a situation that 
	 * only one literal is left, the literal will be add to assertLiterals.      
	 */
	private long firstRefine() {
		long cost = 1;
		boolean assertChanged = false;
		Set<Clause> res = new HashSet<Clause>();
		Iterator<Clause> it = clauses.iterator();
		while (it.hasNext()) {
			Clause c = (it.next());
			c.firstRefine();
			long cCost = c.cost();
			if (cCost == 0) {cost = 0;res.clear();break;}
			if (cCost == -1) {continue;}
			if (c.literals.size() == 1) {
				assertChanged = true;
				assertLiterals = assertLiterals.union(c.literals);
			} 
			else res.add(c);
			cost = cost * cCost;
		}
		clauses = res;
		if(cost==0)return 0;
		if (res.size() == 0 && !assertChanged)return -1;
		return cost;
	}

	/** A sat() procedure with back searching */
/*    private long secondRefineX(SetOfTerm assertLits, Map cache, Object[] cls,
                              int index) {
        long cost = 1;
        for ( int i = index; i < cls.length; i++ ) {
            Clause c = (Clause)cls[i];
            final SetOfTerm ls = c.refine ( assertLits, cache );
            if ( ls.contains ( falseT ) ) return 0;
            if ( ls.contains ( trueT ) )
                return secondRefine ( assertLits, cache, cls, i + 1 );
            final IteratorOfTerm it = ls.iterator ();
            while ( it.hasNext () ) {
                SetOfTerm nextLits = SetAsListOfTerm.EMPTY_SET.union ( assertLits );
                nextLits = nextLits.add ( it.next () );
                final Map nextCache = new HashMap ();
                nextCache.putAll ( cache );
                long nextCost = secondRefine ( nextLits, nextCache, cls, i + 1 );
                cost = cost + nextCost;

            }
        }
        return cost;
    } */

	private class Clause {

		/**all literals contains in this clause*/
		public SetOfTerm literals = SetAsListOfTerm.EMPTY_SET;

		public Clause(SetOfTerm lits) {
			literals = lits;
		}

		public IteratorOfTerm iterator() {
			return literals.iterator();
		}

		/**
		 * @return 0 if this clause is refine to false. 1 if true. 
		 * Otherwise,return the number of literals it left.
		 */
		public long cost() {
			if (literals.contains(falseT) && literals.size() == 1)
				return 0;
			if (literals.contains(trueT))
				return -1;
			int cost = literals.size();
			return cost;
		}

		/** Refine this clause in two process, first try to refined by 
		 * itself, @see selfRefine. Second refine this clause by assuming
		 * assertLiteras are true*/
		public void firstRefine() {
		//	if (selfRefine(literals)) {
		//		literals = SetAsListOfTerm.EMPTY_SET.add(trueT);
		//		return;
		//	}
			literals = this.refine(assertLiterals);
		}
             
		/**
		 * Refine literals in this clause, but it does not change 
		 * literlas, only return literals that can't be removed by
		 * refining
		 */
		public SetOfTerm refine(SetOfTerm assertLits) {
			SetOfTerm res = SetAsListOfTerm.EMPTY_SET;
			IteratorOfTerm it = this.iterator();
			while (it.hasNext()) {
				Term lit = it.next();
				Term temp = proveLiteral(lit, assertLits);
				final Operator op = temp.op();
                if (op == Op.TRUE) {
					res = SetAsListOfTerm.EMPTY_SET.add(trueT);
					break;
				}
				if (op == Op.FALSE) {
					continue;
				}
				res = res.add(lit);
			}
			if (res.size() == 0)
				res = res.add(falseT);
			return res;
		}

		
		/**This method is used for detect where a clause can be simply 
		 * refined to to true. And it is implemented like this. Assume
		 * that the clause contains two literals Li and Lj. If (!Li->Lj) 
		 * which is acturally (Li|Lj), is true, and the clasue is true.
		 * provedByAnthoer(Lj,!Li) is used to proved (!Li->Lj). Some 
		 * examples are (!a|a) which is (!!a->a) and (a>=1|a<=0) which is
		 * !a>=1->a<=0      
		 */
		public boolean selfRefine(SetOfTerm lits) {
			if(lits.size()<=1)return false;
			Term[] terms = lits.toArray();
			SetOfTerm next = lits.remove(terms[0]);
			boolean opNot    = terms[0].op()==Op.NOT;
			Term axiom = opNot?terms[0].sub(0): tb.not(terms[0]);
			for(int j=1;j<terms.length ;j++){
			     Term pro = provedByAnother(terms[j],axiom);
			     final Operator op = pro.op();
                 if(op == Op.TRUE)return true;
			     if(op == Op.FALSE&&terms[0].equals(terms[j])){
				next = next.remove(terms[j]);
			        literals = literals.remove(terms[j]);
			     }
			}
			return selfRefine(next);
		}
		
		
		public String toString() {
			return literals.toString();
		}
    }

}
