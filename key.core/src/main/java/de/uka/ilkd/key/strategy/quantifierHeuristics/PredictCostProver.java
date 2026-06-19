/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;
import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

/**
 * TODO: rewrite, this seems pretty inefficient ...
 */
public class PredictCostProver {

    private final TermBuilder tb;

    private final JTerm trueT, falseT;

    /** assume that all literal in <code>assertLiterals</code> are true */
    private ImmutableSet<JTerm> assertLiterals;

    /** clauses from <code>instance</code> of CNF */
    private Set<Clause> clauses = new LinkedHashSet<>();

    private final Services services;

    private PredictCostProver(JTerm instance, ImmutableSet<JTerm> assertList, Services services) {
        this.assertLiterals = assertList;
        this.services = services;
        this.tb = services.getTermBuilder();
        this.trueT = tb.tt();
        this.falseT = tb.ff();
        initClauses(instance);
    }

    public static long computerInstanceCost(Substitution sub, JTerm matrix,
            ImmutableSet<JTerm> assertList, Services services) {

        if (!sub.isGround()) {
            // non-ground substitutions not supported yet
            return -1;
        } else {
            final PredictCostProver prover = new PredictCostProver(
                (JTerm) sub.applyWithoutCasts(matrix, services), assertList, services);
            return prover.cost();
        }
    }

    // init context
    private void initClauses(JTerm instance) {

        for (var t : TriggerUtils.setByOperator(instance, Junctor.AND)) {
            for (ImmutableSet<JTerm> lit : createClause(
                TriggerUtils.setByOperator(t, Junctor.OR))) {
                clauses.add(new Clause(lit));
            }
        }
    }

    private ImmutableSet<ImmutableSet<JTerm>> createClause(
            ImmutableSet<org.key_project.logic.Term> set) {
        final ImmutableSet<ImmutableSet<JTerm>> nil = DefaultImmutableSet.nil();
        ImmutableSet<ImmutableSet<JTerm>> res = nil.add(DefaultImmutableSet.<JTerm>nil());
        for (var t : set) {
            ImmutableSet<ImmutableSet<JTerm>> tmp = nil;
            for (ImmutableSet<JTerm> cl : res) {
                tmp = tmp.add(cl.add((JTerm) t));
            }
            res = tmp;
        }
        return res;
    }

    // end

    // (2)self-proved rule
    /**
     * If the given <code>problem</code>'s operation is equal,or mathmetic operation(=,>=, <=), this
     * method will try to prove it by finding the relation between its two subterms.
     */
    private JTerm provedBySelf(JTerm problem) {
        boolean negated = false;
        JTerm pro = problem;
        Operator op = pro.op();
        while (op == Junctor.NOT) {
            negated = !negated;
            pro = pro.sub(0);
            op = pro.op();
        }
        if ((op == Equality.EQUALS || op == Equality.EQV)) {
            Term term = pro.sub(0);
            Term formula = pro.sub(1);
            if (RENAMING_TERM_PROPERTY.equalsModThisProperty(term, formula)) {
                return negated ? falseT : trueT;
            }
        }
        JTerm arithRes = HandleArith.provedByArith(pro, services);
        if (TriggerUtils.isTrueOrFalse(arithRes)) {
            return negated ? tb.not(arithRes) : arithRes;
        } else {
            return problem;
        }
    }

    // (3)equal rule
    /***
     * @return trueT if problem is equal axiom, false if problem's negation is equal axiom.
     *         Otherwise retrun problem.
     */
    private JTerm directConsequenceOrContradictionOfAxiom(JTerm problem, JTerm axiom) {
        boolean negated = false;
        JTerm pro = problem;
        while (pro.op() == Junctor.NOT) {
            pro = pro.sub(0);
            negated = !negated;
        }
        JTerm ax = axiom;
        while (ax.op() == Junctor.NOT) {
            ax = ax.sub(0);
            negated = !negated;
        }
        if (RENAMING_TERM_PROPERTY.equalsModThisProperty(pro, ax)) {
            return negated ? falseT : trueT;
        }
        return problem;
    }

    // (4)combine provedByequal and provedByArith .
    /**
     * @param problem
     * @param axiom
     * @return if axiom conduct problem then return trueT. If axiom conduct negation of problem
     *         return fastT. Otherwise, return problem
     */
    private JTerm provedByAnother(JTerm problem, JTerm axiom) {
        JTerm res = directConsequenceOrContradictionOfAxiom(problem, axiom);
        if (TriggerUtils.isTrueOrFalse(res)) {
            return res;
        }
        return HandleArith.provedByArith(problem, axiom, services);
    }

    // (5) combine rules
    /**
     * try to prove <code>problem</code> by know <code>assertLits</code>
     *
     * @param problem a literal to be proved
     * @param assertLits a set of term assertLiterals in which all literals are true
     * @return return <code>trueT</code> if if formu is proved to true, <code> falseT</code> if
     *         false, and <code>atom</code> if it cann't be proved.
     */
    private JTerm proveLiteral(JTerm problem, Iterable<? extends JTerm> assertLits) {
        JTerm res;
        /*
         * res = provedFromCache(problem, cache); if (res.equals(trueT) || res.equals(falseT)) {
         * return res; }
         */
        res = provedBySelf(problem);
        if (TriggerUtils.isTrueOrFalse(res)) {
            // addToCache(problem,res,cache);
            return res;
        }
        for (JTerm t : assertLits) {
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
     * refine every clause, by assume assertList are true and if a clause's cost is 0 which means it
     * is refined to false, then cost 0 returned. If every clause's cost is -1 which means every
     * clause is refined to true, cost -1 returned. Otherwise, multiply of every cost is return.
     * Beside, if a clause is refined to a situation that only one literal is left, the literal will
     * be add to assertLiterals.
     */
    private long firstRefine() {
        long cost = 1;
        boolean assertChanged = false;
        Set<Clause> res = new LinkedHashSet<>();
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
        if (cost == 0) {
            return 0;
        }
        if (res.isEmpty() && !assertChanged) {
            return -1;
        }
        return cost;
    }

    /** A sat() procedure with back searching */
    /*
     * private long secondRefineX(SetOf<Term> assertLits, Map cache, Object[] cls, int index) { long
     * cost = 1; for ( int i = index; i < cls.length; i++ ) { Clause c = (Clause)cls[i]; final
     * SetOf<Term> ls = c.refine ( assertLits, cache ); if ( ls.contains ( falseT ) ) return 0; if (
     * ls.contains ( trueT ) ) return secondRefine ( assertLits, cache, cls, i + 1 ); final
     * Iterator<Term> it = ls.iterator (); while ( it.hasNext () ) { SetOf<Term> nextLits =
     * SetAsListOf.<Term>nil().union ( assertLits ); nextLits = nextLits.add ( it.next () ); final
     * Map nextCache = new HashMap (); nextCache.putAll ( cache ); long nextCost = secondRefine (
     * nextLits, nextCache, cls, i + 1 ); cost = cost + nextCost;
     *
     * } } return cost; }
     */

    private class Clause implements Iterable<JTerm> {

        /** all literals contains in this clause */
        private ImmutableSet<JTerm> literals;

        public Clause(ImmutableSet<JTerm> lits) {
            literals = lits;
        }

        @Override
        public boolean equals(Object o) {
            if (!(o instanceof Clause other)) {
                return false;
            }
            if (other.literals.size() != literals.size()) {
                return false;
            }
            return literals.equals(other.literals);
        }

        @Override
        public int hashCode() {
            return literals.hashCode();
        }

        @Override
        public Iterator<JTerm> iterator() {
            return literals.iterator();
        }

        /**
         * @return 0 if this clause is refine to false. 1 if true. Otherwise,return the number of
         *         literals it left.
         */
        public long cost() {
            if (literals.size() == 1 && literals.contains(falseT)) {
                return 0;
            }
            if (literals.contains(trueT)) {
                return -1;
            }
            return literals.size();
        }

        /**
         * Refine this clause in two process, first try to refined by itself, @see selfRefine.
         * Second refine this clause by assuming assertLiteras are true
         */
        public void firstRefine() {
            // if (selfRefine(literals)) {
            // literals = SetAsListOf.<Term>nil().add(trueT);
            // return;
            // }
            literals = this.refine(assertLiterals);
        }

        /**
         * Refine literals in this clause, but it does not change literlas, only return literals
         * that can't be removed by refining
         */
        public ImmutableSet<JTerm> refine(Iterable<? extends JTerm> assertLits) {
            ImmutableSet<JTerm> res = DefaultImmutableSet.nil();
            for (final JTerm lit : this) {
                final Operator op = proveLiteral(lit, assertLits).op();
                if (op == Junctor.TRUE) {
                    res = DefaultImmutableSet.<JTerm>nil().add(trueT);
                    break;
                }
                if (op == Junctor.FALSE) {
                    continue;
                }
                res = res.add(lit);
            }
            if (res.size() == 0) {
                res = res.add(falseT);
            }
            return res;
        }

        /**
         * This method is used for detect where a clause can be simply refined to to true. And it is
         * implemented like this. Assume that the clause contains two literals Li and Lj. If
         * (!Li->Lj) which is acturally (Li|Lj), is true, and the clasue is true.
         * provedByAnthoer(Lj,!Li) is used to proved (!Li->Lj). Some examples are (!a|a) which is
         * (!!a->a) and (a>=1|a<=0) which is !a>=1->a<=0
         */
        public boolean selfRefine(ImmutableSet<JTerm> lits) {
            if (lits.size() <= 1) {
                return false;
            }
            JTerm[] terms = lits.toArray(new JTerm[lits.size()]);
            ImmutableSet<JTerm> next = lits.remove(terms[0]);
            boolean opNot = terms[0].op() == Junctor.NOT;
            JTerm axiom = opNot ? terms[0].sub(0) : tb.not(terms[0]);
            for (int j = 1; j < terms.length; j++) {
                JTerm pro = provedByAnother(terms[j], axiom);
                final Operator op = pro.op();
                if (op == Junctor.TRUE) {
                    return true;
                }
                if (op == Junctor.FALSE
                        && terms[0].equalsModProperty(terms[j], IRRELEVANT_TERM_LABELS_PROPERTY)) {
                    next = next.remove(terms[j]);
                    literals = literals.remove(terms[j]);
                }
            }
            return selfRefine(next);
        }

        @Override
        public String toString() {
            return literals.toString();
        }
    }

}
