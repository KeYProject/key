/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics.theory;


import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.strategy.quantifierHeuristics.Substitution;
import de.uka.ilkd.key.strategy.quantifierHeuristics.constraint.Constraint;
import de.uka.ilkd.key.strategy.quantifierHeuristics.constraint.EqualityConstraint;
import de.uka.ilkd.key.strategy.quantifierHeuristics.constraint.Metavariable;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableSet;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

/**
 * Support for the equality theory.
 *
 * Forbids the equality {@code =} as a trigger (matching on it has not been observed to help
 * instantiation) and provides no derived triggers. For cost prediction it decides a literal that is
 * an equality or equivalence whose two sides are equal up to renaming, and decides an arbitrary
 * literal that equals an assumed one up to renaming (or contradicts it under a negation).
 */
final class EqualityTheorySupport implements QuantifierTheorySupport {

    /**
     * Forbids the equality {@code =} as a trigger.
     *
     * @param candidate a trigger candidate that contains the quantified variables
     * @param enclosing the term the candidate is an argument of, null at the top of a literal
     * @param services access to the theory operators
     * @return the verdict
     */
    @Override
    public CandidateVerdict verdictOn(JTerm candidate, JTerm enclosing, Services services) {
        return candidate.op() == Equality.EQUALS ? CandidateVerdict.FORBIDDEN
                : CandidateVerdict.ACCEPTABLE;
    }

    /**
     * Provides no derived triggers.
     *
     * @param term an accepted trigger term
     * @param clauseVariables the quantified variables of the clause the trigger belongs to
     * @param services access to the theory operators
     * @return the empty list
     */
    @Override
    public List<JTerm> provideTriggers(JTerm term,
            ImmutableSet<QuantifiableVariable> clauseVariables, Services services,
            MetavariableFactory metavariableFactory) {
        return List.of();
    }

    /**
     * Checks whether the literal is an equality or equivalence whose two sides are equal up to
     * renaming.
     *
     * @param strippedLiteral a literal without leading negations
     * @param services access to the theory operators
     * @return {@code PROVED} if the two sides are equal up to renaming, otherwise {@code UNKNOWN}
     */
    @Override
    public LiteralDecision decideStrippedSelf(JTerm strippedLiteral, Services services) {
        final Operator op = strippedLiteral.op();
        if (op == Equality.EQUALS || op == Equality.EQV) {
            if (RENAMING_TERM_PROPERTY.equalsModThisProperty(strippedLiteral.sub(0),
                strippedLiteral.sub(1))) {
                return LiteralDecision.PROVED;
            }
        }
        return LiteralDecision.UNKNOWN;
    }

    /**
     * Checks whether the literal follows from the axiom by equality up to renaming. Leading
     * negations of both are tracked, so an axiom equal to the negated literal refutes it.
     *
     * @param literal a literal to decide
     * @param axiom a literal assumed to be true
     * @param services access to the theory operators
     * @return {@code PROVED} if the axiom equals the literal, {@code REFUTED} if it equals its
     *         negation, otherwise {@code UNKNOWN}
     */
    @Override
    public LiteralDecision decideFromAxiom(JTerm literal, JTerm axiom, Services services) {
        boolean negated = false;
        JTerm pro = literal;
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
            return negated ? LiteralDecision.REFUTED : LiteralDecision.PROVED;
        }
        return LiteralDecision.UNKNOWN;
    }

    @Override
    public List<JTerm> fallbackTriggers(ClauseTriggers selection, Services services,
            MetavariableFactory metavariableFactory) {
        List<JTerm> fallbackTriggers = new ArrayList<>();
        final ClauseAnalysis clauseInfo = selection.clause();

        final TermBuilder tb = services.getTermBuilder();
        final Map<QuantifiableVariable, Term> qv2mv = new LinkedHashMap<>();
        final Map<Metavariable, QuantifiableVariable> mv2qv = new LinkedHashMap<>();
        for (QuantifiableVariable var : clauseInfo.clause().freeVars()) {
            final Metavariable mv = metavariableFactory.fresh(var.sort());
            qv2mv.put(var, tb.var(mv));
            if (clauseInfo.universalVariables().contains(var)) {
                mv2qv.put(mv, var);
            }
        }
        final Substitution qv2mvSubst = new Substitution(DefaultImmutableMap.fromMap(qv2mv));
        final OpReplacer mv2qvReplacer =
            new OpReplacer(mv2qv, services.getTermFactory());
        for (JTerm lit : clauseInfo.literals()) {
            if (lit.op() == Equality.EQUALS) {
                fallbackTriggers.addAll(
                    solveEquation(mv2qv.keySet(), qv2mvSubst, mv2qvReplacer, lit, services));
            }
        }
        return fallbackTriggers;
    }

    /// solves equation f(u) = f(g(v)) to u = g(MV_V)
    /// @param mvs set of Metavariables used to replace **universal** bound variables
    /// @param qv2mv substitution of the free variables of lit by their meta variables
    /// @param mv2qv OpReplacer to restore universal (not existential) bound variables
    /// @param lit the JTerm representing an uncovered literal
    /// @param services the Services class provides access to term construction and other services
    /// @return list of solved equations that describe triggers
    private List<JTerm> solveEquation(Set<Metavariable> mvs, Substitution qv2mv,
            OpReplacer mv2qv, JTerm lit,
            Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final JTerm litWithMV = (JTerm) qv2mv.applyWithoutCasts(lit, services);
        final Constraint c =
            EqualityConstraint.BOTTOM.unify(litWithMV.sub(0), litWithMV.sub(1), services);
        List<JTerm> solvedEquations = new ArrayList<>();
        if (c.isSatisfiable()) {
            for (final Metavariable mv : mvs) {
                final JTerm solution = c.getInstantiation(mv, services);
                final Operator instOp = solution.op();
                if (instOp instanceof LogicVariable ||
                        instOp instanceof Metavariable) {
                    // solutions that are a variable
                    // and contain no function symbol do not
                    // make useful triggers
                    continue;
                }
                final JTerm solvedEquation = mv2qv.replace(tb.equals(tb.var(mv), solution));
                solvedEquations.add(solvedEquation);
                solvedEquations.add(tb.equals(solvedEquation.sub(1), solvedEquation.sub(0)));
            }
        }
        return solvedEquations;
    }
}
