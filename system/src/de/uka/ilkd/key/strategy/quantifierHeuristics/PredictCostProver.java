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

package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * TODO: rewrite, this seems pretty inefficient ...
 */
public class PredictCostProver {

    private final static TermBuilder tb = TermBuilder.DF;

    private final static Term trueT = tb.tt(), falseT = tb.ff();

    /** assume that all literal in <code>assertLiterals</code> are true */
    private ImmutableSet<Term> assertLiterals;
    
    /** clauses from <code>instance</code> of CNF */
    private Set<Clause> clauses = new LinkedHashSet<Clause>();

    private Services services;

    private PredictCostProver(Term instance, ImmutableSet<Term> assertList,
	    Services services) {
	this.assertLiterals = assertList;
	this.services = services;
	initClauses(instance);
    }

    public static long computerInstanceCost(Substitution sub, Term matrix,
	    ImmutableSet<Term> assertList, Services services) {

	if (!sub.isGround()) {
	    // non-ground substitutions not supported yet
	    return -1;
	} else {
	    final PredictCostProver prover = new PredictCostProver(sub
		.applyWithoutCasts(matrix, services), assertList, services);
	    return prover.cost();
	}
    }

    // init context
    private void initClauses(Term instance) {

	for (Term t : TriggerUtils.setByOperator(instance, Junctor.AND)) {
 	    for (ImmutableSet<Term> lit : createClause(TriggerUtils.setByOperator(t, Junctor.OR))) {
		clauses.add(new Clause(lit));
	    }
	}
    }

    private ImmutableSet<ImmutableSet<Term>> createClause(ImmutableSet<Term> set)  {
	final DefaultImmutableSet<ImmutableSet<Term>> nil = 
	    DefaultImmutableSet.<ImmutableSet<Term>>nil();	
	ImmutableSet<ImmutableSet<Term>> res = nil.add(DefaultImmutableSet.<Term>nil());
	for (Term t : set) {	    
            ImmutableSet<ImmutableSet<Term>> tmp = nil;
	    for (ImmutableSet<Term> cl : res) {
		tmp = createClauseHelper(tmp, t, cl);
	    }
	    res = tmp;
	}
	return res;
    }

    private ImmutableSet<ImmutableSet<Term>> createClauseHelper(ImmutableSet<ImmutableSet<Term>> res, 
	    Term self, ImmutableSet<Term> ts) {
	res = res.add(ts.add(self));
	return res;
    }

    // end

    // (2)self-proved rule
    /**
     * If the given <code>problem</code>'s operation is equal,or mathmetic
     * operation(=,>=, <=), this method will try to prove it by finding the
     * relation between its two subterms.
     */
    private Term provedBySelf(Term problem) {
	boolean negated = false;
	Term pro = problem;
	Operator op = pro.op();
	while (op == Junctor.NOT) {
	    negated = !negated;
	    pro = pro.sub(0);
	    op = pro.op();
	}
	if ((op == Equality.EQUALS || op == Equality.EQV) && 
		pro.sub(0).equalsModRenaming(pro.sub(1)))
	    return negated ? falseT : trueT;
	Term arithRes = HandleArith.provedByArith(pro, services);
	if (TriggerUtils.isTrueOrFalse(arithRes))
	    return negated ? tb.not(arithRes) : arithRes;
	else
	    return problem;
    }

    // (3)equal rule
    /***
     * @return trueT if problem is equal axiom, false if problem's negation is
     *         equal axiom. Otherwise retrun problem.
     */
    private Term directConsequenceOrContradictionOfAxiom(Term problem, Term axiom) {
	boolean negated = false;
	Term pro = problem;
	while (pro.op() == Junctor.NOT) {
	    pro = pro.sub(0);
	    negated = !negated;
	}
	Term ax = axiom;
	while (ax.op() == Junctor.NOT) {
	    ax = ax.sub(0);
	    negated = !negated;
	}
	if (pro.equalsModRenaming(ax))
	    return negated ? falseT : trueT;
	return problem;
    }

    // (4)combine provedByequal and provedByArith .
    /**
     * @param problem
     * @param axiom
     * @return if axiom conduct problem then return trueT. If axiom conduct
     *         negation of problem return fastT. Otherwise, return problem
     */
    private Term provedByAnother(Term problem, Term axiom) {
	Term res = directConsequenceOrContradictionOfAxiom(problem, axiom);
	if (TriggerUtils.isTrueOrFalse(res))
	    return res;
	return HandleArith.provedByArith(problem, axiom, services);
    }

    // (5) combine rules
    /**
     * try to prove <code>problem</code> by know <code>assertLits</code>
     * 
     * @param problem
     *            a literal to be proved
     * @param assertLits
     *            a set of term assertLiterals in which all literals are true
     * @return return <code>trueT</code> if if formu is proved to true,
     *         <code> falseT</code> if false, and <code>atom</code> if it cann't
     *         be proved.
     */
    private Term proveLiteral(Term problem, Iterable<? extends Term> assertLits) {
	Term res;
	/*
	 * res = provedFromCache(problem, cache); if (res.equals(trueT) ||
	 * res.equals(falseT)) { return res; }
	 */
	res = provedBySelf(problem);
	if (TriggerUtils.isTrueOrFalse(res)) {
	    // addToCache(problem,res,cache);
	    return res;
	}
	for (Term t : assertLits) {
	    res = provedByAnother(problem, t);
	    if (TriggerUtils.isTrueOrFalse(res)) {
		// addToCache(problem, res,cache);
		return res;
	    }
	}
	return problem;
    }

    // end

    // cost computation
    /** do two step refinement and return the cost */
    private long cost() {
	return firstRefine();
    }

    /**
     * refine every clause, by assume assertList are true and if a clause's cost
     * is 0 which means it is refined to false, then cost 0 returned. If every
     * clause's cost is -1 which means every clause is refined to true, cost -1
     * returned. Otherwise, multiply of every cost is return. Beside, if a
     * clause is refined to a situation that only one literal is left, the
     * literal will be add to assertLiterals.
     */
    private long firstRefine() {
	long cost = 1;
	boolean assertChanged = false;
	Set<Clause> res = new LinkedHashSet<Clause>();
	for (final Clause c : clauses) {
	    c.firstRefine();
	    long cCost = c.cost();
	    if (cCost == 0) {
		cost = 0;
		res.clear();
		break;
	    }
	    if (cCost == -1) {
		continue;
	    }
	    if (c.literals.size() == 1) {
		assertChanged = true;
		assertLiterals = assertLiterals.union(c.literals);
	    } else {
		res.add(c);
	    }
	    cost = cost * cCost;
	}
	clauses = res;
	if (cost == 0)
	    return 0;
	if (res.isEmpty() && !assertChanged)
	    return -1;
	return cost;
    }

    /** A sat() procedure with back searching */
    /*
     * private long secondRefineX(SetOf<Term> assertLits, Map cache, Object[]
     * cls, int index) { long cost = 1; for ( int i = index; i < cls.length; i++
     * ) { Clause c = (Clause)cls[i]; final SetOf<Term> ls = c.refine (
     * assertLits, cache ); if ( ls.contains ( falseT ) ) return 0; if (
     * ls.contains ( trueT ) ) return secondRefine ( assertLits, cache, cls, i +
     * 1 ); final Iterator<Term> it = ls.iterator (); while ( it.hasNext () ) {
     * SetOf<Term> nextLits = SetAsListOf.<Term>nil().union ( assertLits );
     * nextLits = nextLits.add ( it.next () ); final Map nextCache = new HashMap
     * (); nextCache.putAll ( cache ); long nextCost = secondRefine ( nextLits,
     * nextCache, cls, i + 1 ); cost = cost + nextCost;
     * 
     * } } return cost; }
     */

    private class Clause implements Iterable<Term>{

	/** all literals contains in this clause */
	public ImmutableSet<Term> literals = DefaultImmutableSet.<Term> nil();

	public Clause(ImmutableSet<Term> lits) {
	    literals = lits;
	}	
	
	public boolean equals(Object o) {
	    if (!(o instanceof Clause)) return false;
	    final Clause other = (Clause) o;
	    if (other.literals.size() != literals.size()) {
		return false;
	    }
	    return literals.equals(other.literals);
	}
	
	public int hashCode() {
	    return literals.hashCode();
	}

	public Iterator<Term> iterator() {
	    return literals.iterator();
	}

	/**
	 * @return 0 if this clause is refine to false. 1 if true.
	 *         Otherwise,return the number of literals it left.
	 */
	public long cost() {
	    if (literals.size() == 1 && literals.contains(falseT))
		return 0;
	    if (literals.contains(trueT))
		return -1;
	    return literals.size();
	}

	/**
	 * Refine this clause in two process, first try to refined by itself, @see
	 * selfRefine. Second refine this clause by assuming assertLiteras are
	 * true
	 */
	public void firstRefine() {
	    // if (selfRefine(literals)) {
	    // literals = SetAsListOf.<Term>nil().add(trueT);
	    // return;
	    // }
	    literals = this.refine(assertLiterals);
	}

	/**
	 * Refine literals in this clause, but it does not change literlas, only
	 * return literals that can't be removed by refining
	 */
	public ImmutableSet<Term> refine(Iterable<? extends Term> assertLits) {
	    ImmutableSet<Term> res = DefaultImmutableSet.<Term> nil();
	    for (final Term lit : this) {
		final Operator op = proveLiteral(lit, assertLits).op();
		if (op == Junctor.TRUE) {
		    res = DefaultImmutableSet.<Term> nil().add(trueT);
		    break;
		}
		if (op == Junctor.FALSE) {
		    continue;
		}
		res = res.add(lit);
	    }
	    if (res.size() == 0)
		res = res.add(falseT);
	    return res;
	}

	/**
	 * This method is used for detect where a clause can be simply refined
	 * to to true. And it is implemented like this. Assume that the clause
	 * contains two literals Li and Lj. If (!Li->Lj) which is acturally
	 * (Li|Lj), is true, and the clasue is true. provedByAnthoer(Lj,!Li) is
	 * used to proved (!Li->Lj). Some examples are (!a|a) which is (!!a->a)
	 * and (a>=1|a<=0) which is !a>=1->a<=0
	 */
	public boolean selfRefine(ImmutableSet<Term> lits) {
	    if (lits.size() <= 1)
		return false;
	    Term[] terms = lits.toArray(new Term[lits.size()]);
	    ImmutableSet<Term> next = lits.remove(terms[0]);
	    boolean opNot = terms[0].op() == Junctor.NOT;
	    Term axiom = opNot ? terms[0].sub(0) : tb.not(terms[0]);
	    for (int j = 1; j < terms.length; j++) {
		Term pro = provedByAnother(terms[j], axiom);
		final Operator op = pro.op();
		if (op == Junctor.TRUE)
		    return true;
		if (op == Junctor.FALSE && terms[0].equals(terms[j])) {
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
