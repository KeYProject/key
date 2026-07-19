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
import de.uka.ilkd.key.logic.op.Junctor;

import org.key_project.logic.op.Operator;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

/**
 * Predicts the cost of instantiating a quantified formula with a candidate term. The instantiated
 * matrix is read as a conjunction of clauses. Each clause is refined against the literals already
 * known true on the sequent, dropping a literal that is false and marking the clause true once one
 * of its literals is proved. The predicted cost combines the sizes of the clauses that remain, so
 * an instantiation that leaves fewer open clauses is cheaper.
 */
public class PredictCostProver {

    private final TermBuilder tb;

    private final JTerm trueT, falseT;

    /** The literals assumed to be true on the sequent. */
    private ImmutableSet<JTerm> assertLiterals;

    /** The clauses of the instantiated matrix, a conjunction of disjunctions. */
    private Set<Clause> clauses = new LinkedHashSet<>();

    private final Services services;

    /**
     * Equality reasoning over the sequent's assumed equalities, built once and shared across the
     * cost predictions of all candidate instantiations. Lets a clause literal already satisfied by
     * an assumed equality be recognised, so the instance is not proposed as a useful step.
     */
    private final Congruence congruence;

    private PredictCostProver(JTerm instance, ImmutableSet<JTerm> assertList, Congruence congruence,
            Services services) {
        this.assertLiterals = assertList;
        this.congruence = congruence;
        this.services = services;
        this.tb = services.getTermBuilder();
        this.trueT = tb.tt();
        this.falseT = tb.ff();
        initClauses(instance);
    }

    /**
     * Predicts the cost of instantiating a quantified formula's matrix with a candidate
     * substitution.
     *
     * @param sub a ground substitution for the quantified variables
     * @param matrix the matrix of the quantified formula
     * @param assertList the literals assumed to be true on the sequent, already normalised through
     *        {@code congruence}
     * @param congruence equality reasoning over the sequent's assumed equalities
     * @param services access to the theory operators
     * @return the predicted cost, or -1 if the substitution is not ground or every clause is proved
     *         true
     */
    static long computerInstanceCost(Substitution sub, JTerm matrix,
            ImmutableSet<JTerm> assertList, Congruence congruence, Services services) {

        if (!sub.isGround()) {
            // non-ground substitutions not supported yet
            return -1;
        } else {
            final PredictCostProver prover = new PredictCostProver(
                (JTerm) sub.applyWithoutCasts(matrix, services), assertList, congruence, services);
            return prover.cost();
        }
    }

    /**
     * The axioms of one sequent prepared for repeated predictions: the congruence built from
     * them and the literals normalized by it. Opaque outside this package, so the congruence
     * type stays internal; build once per sequent and reuse for every candidate instance.
     */
    public static final class PreparedAxioms {
        private final Congruence congruence;
        private final ImmutableSet<JTerm> normalized;

        private PreparedAxioms(Congruence congruence, ImmutableSet<JTerm> normalized) {
            this.congruence = congruence;
            this.normalized = normalized;
        }
    }

    /**
     * Prepares the given literals for repeated predictions over one sequent.
     *
     * @param assertList the literals assumed to be true on the sequent
     * @param services access to the theory operators
     * @return the prepared axioms
     */
    public static PreparedAxioms prepare(ImmutableSet<JTerm> assertList, Services services) {
        final Congruence congruence = new Congruence(assertList, services);
        ImmutableSet<JTerm> normalized = assertList;
        if (!congruence.isTrivial()) {
            ImmutableSet<JTerm> res = DefaultImmutableSet.nil();
            for (final JTerm lit : assertList) {
                res = res.add(congruence.normalize(lit));
            }
            normalized = res;
        }
        return new PreparedAxioms(congruence, normalized);
    }

    /**
     * As the congruence-taking entry point, with the axioms prepared by {@link #prepare}.
     *
     * @param sub a ground substitution for the quantified variables
     * @param matrix the matrix of the quantified formula
     * @param axioms the prepared axioms of the sequent
     * @param services access to the theory operators
     * @return the predicted cost, or -1 if the substitution is not ground or every clause is
     *         proved true
     */
    public static long computerInstanceCost(Substitution sub, JTerm matrix, PreparedAxioms axioms,
            Services services) {
        return computerInstanceCost(sub, matrix, axioms.normalized, axioms.congruence, services);
    }

    /**
     * Convenience entry point for callers without a shared congruence: builds one from
     * {@code assertList} and normalises the literals, then predicts the cost. The quantifier
     * instantiation path shares one congruence per sequent instead and calls the overload above.
     *
     * @param sub a ground substitution for the quantified variables
     * @param matrix the matrix of the quantified formula
     * @param assertList the literals assumed to be true on the sequent
     * @param services access to the theory operators
     * @return the predicted cost
     */
    public static long computerInstanceCost(Substitution sub, JTerm matrix,
            ImmutableSet<JTerm> assertList, Services services) {
        return computerInstanceCost(sub, matrix, prepare(assertList, services), services);
    }

    /** Splits the instantiated matrix into its clauses. */
    private void initClauses(JTerm instance) {

        for (var t : TriggerUtils.setByOperator(instance, Junctor.AND)) {
            for (ImmutableSet<JTerm> lit : createClause(
                TriggerUtils.setByOperator(t, Junctor.OR))) {
                clauses.add(new Clause(lit));
            }
        }
    }

    /**
     * Gathers the disjuncts of a clause into a literal set.
     *
     * @param set the disjuncts of a clause
     * @return the clause's literals, wrapped in a one-element set
     */
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

    /**
     * Checks whether <code>problem</code> holds on its own. The literal is stripped of its leading
     * negations and offered to each theory support; the first support that reaches a verdict wins,
     * and the stripped negations are re-applied to it.
     *
     * @param problem the literal to decide
     * @return <code>trueT</code> if the literal is proved true, <code>falseT</code> if proved
     *         false,
     *         and <code>problem</code> if undecided
     */
    private JTerm provedBySelf(JTerm problem) {
        boolean negated = false;
        JTerm pro = problem;
        while (pro.op() == Junctor.NOT) {
            negated = !negated;
            pro = pro.sub(0);
        }
        for (final QuantifierTheorySupport support : TriggersSet.THEORY_SUPPORTS) {
            QuantifierTheorySupport.LiteralDecision decision =
                support.decideStrippedSelf(pro, services);
            if (decision != QuantifierTheorySupport.LiteralDecision.UNKNOWN) {
                if (negated) {
                    decision = decision.negate();
                }
                return decision == QuantifierTheorySupport.LiteralDecision.PROVED ? trueT : falseT;
            }
        }
        return problem;
    }

    /**
     * Checks whether <code>problem</code> follows from the assumed-true <code>axiom</code> by
     * offering both to each theory support. The first support that reaches a verdict wins.
     *
     * @param problem the literal to decide
     * @param axiom a literal assumed to be true
     * @return <code>trueT</code> if the axiom proves the problem, <code>falseT</code> if it proves
     *         the problem's negation, and <code>problem</code> if undecided
     */
    private JTerm provedByAnother(JTerm problem, JTerm axiom) {
        for (final QuantifierTheorySupport support : TriggersSet.THEORY_SUPPORTS) {
            final QuantifierTheorySupport.LiteralDecision decision =
                support.decideFromAxiom(problem, axiom, services);
            if (decision != QuantifierTheorySupport.LiteralDecision.UNKNOWN) {
                return decision == QuantifierTheorySupport.LiteralDecision.PROVED ? trueT : falseT;
            }
        }
        return problem;
    }

    /**
     * Checks whether <code>problem</code> holds, first on its own and then from each assumed
     * literal
     * in turn.
     *
     * @param problem a literal to decide
     * @param assertLits literals assumed to be true
     * @return <code>trueT</code> if the literal is proved true, <code>falseT</code> if proved
     *         false,
     *         and the literal itself if neither
     */
    private JTerm proveLiteral(JTerm problem, Iterable<? extends JTerm> assertLits) {
        final JTerm normProblem = congruence.normalize(problem);
        JTerm res = provedBySelf(normProblem);
        if (TriggerUtils.isTrueOrFalse(res)) {
            return res;
        }
        for (JTerm t : assertLits) {
            res = provedByAnother(normProblem, t);
            if (TriggerUtils.isTrueOrFalse(res)) {
                return res;
            }
        }
        return problem;
    }

    /**
     * Normalises the literals of a clause reduced to a single literal, before it is assumed for the
     * remaining clauses, so later decisions match it modulo the congruence.
     *
     * @param lits the literals to normalise
     * @return the normalised literals, or {@code lits} unchanged when the congruence is trivial
     */
    private ImmutableSet<JTerm> normalizeLiterals(ImmutableSet<JTerm> lits) {
        if (congruence.isTrivial()) {
            return lits;
        }
        ImmutableSet<JTerm> res = DefaultImmutableSet.nil();
        for (final JTerm l : lits) {
            res = res.add(congruence.normalize(l));
        }
        return res;
    }

    /** Returns the predicted cost by refining the clauses against the asserted literals. */
    private long cost() {
        return firstRefine();
    }

    /**
     * Refines every clause against the asserted literals and combines the results into a cost. A
     * clause refined to false makes the whole instance cost 0. Clauses refined to true are dropped.
     * The sizes of the remaining clauses are multiplied. A clause left with a single literal adds
     * that literal to the asserted literals. When every clause is dropped and nothing was added the
     * instance is trivially true and the cost is -1.
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
                assertLiterals = assertLiterals.union(normalizeLiterals(c.literals));
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

    private class Clause implements Iterable<JTerm> {

        /** The literals of this clause. */
        private ImmutableSet<JTerm> literals;

        public Clause(ImmutableSet<JTerm> lits) {
            literals = lits;
        }

        @Override
        public boolean equals(Object o) {
            if (!(o instanceof Clause other)) {
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
         * @return 0 if this clause refined to false, -1 if it refined to true, otherwise the number
         *         of literals it still has
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

        /** Refine this clause by assuming the asserted literals are true. */
        public void firstRefine() {
            literals = this.refine(assertLiterals);
        }

        /**
         * Returns the literals of this clause that refining against the asserted literals cannot
         * remove. A single {@code trueT} means the clause is true, a single {@code falseT} means it
         * is false.
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

        @Override
        public String toString() {
            return literals.toString();
        }
    }

}
