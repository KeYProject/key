/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;

import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableSet;

/**
 * Support for the integer theory.
 *
 * Rejects the (non-strict) comparisons as triggers (matching on them has not been observed to help
 * instantiation) and provides no derived triggers. For cost prediction it decides an arithmetic
 * comparison from itself or from an assumed comparison, through {@link HandleArith}.
 */
final class IntegerTheorySupport implements QuantifierTheorySupport {

    /**
     * Rejects the non-strict comparisons {@code <=} and {@code >=} as triggers.
     *
     * @param candidate a trigger candidate that contains the quantified variables
     * @param services access to the integer theory operators
     * @return whether the candidate is rejected
     */
    @Override
    public boolean rejectsAsTrigger(JTerm candidate, Services services) {
        final Operator op = candidate.op();
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return op == integerLDT.getLessOrEquals() || op == integerLDT.getGreaterOrEquals();
    }

    /**
     * Provides no derived triggers.
     *
     * @param term an accepted trigger term
     * @param clauseVariables the quantified variables of the clause the trigger belongs to
     * @param services access to the integer theory operators
     * @return the empty list
     */
    @Override
    public List<JTerm> provideTriggers(JTerm term,
            ImmutableSet<QuantifiableVariable> clauseVariables, Services services) {
        return List.of();
    }

    /**
     * Checks whether an arithmetic comparison holds on its own, through {@link HandleArith}.
     *
     * @param strippedLiteral a literal without leading negations
     * @param services access to the integer theory operators
     * @return the arithmetic verdict, or {@code UNKNOWN} if undecided
     */
    @Override
    public LiteralDecision decideStrippedSelf(JTerm strippedLiteral, Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return QuantifierTheorySupport
                .fromTruthTerm(HandleArith.provedByArith(strippedLiteral, integerLDT, services));
    }

    /**
     * Checks whether an arithmetic comparison follows from an assumed comparison, through
     * {@link HandleArith}.
     *
     * @param literal a literal to decide
     * @param axiom a literal assumed to be true
     * @param services access to the integer theory operators
     * @return the arithmetic verdict, or {@code UNKNOWN} if undecided
     */
    @Override
    public LiteralDecision decideFromAxiom(JTerm literal, JTerm axiom, Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        return QuantifierTheorySupport
                .fromTruthTerm(HandleArith.provedByArith(literal, axiom, integerLDT, services));
    }

    /**
     * Restricts the equality normalisation on integer terms to what the arithmetic decisions
     * tolerate. A number literal is never rewritten away: it is the concrete value the comparisons
     * in {@link HandleArith} are decided on. A term built by the polynomial operators is left in
     * place in both directions: rewriting it away collapses the structure that
     * {@link de.uka.ilkd.key.rule.metaconstruct.arith.Polynomial} decomposes, and rewriting other
     * terms into it makes it a class representative, which the one-pass normalisation of
     * {@link Congruence} does not rewrite further. Rewriting an atom to a number literal or to
     * another atom stays permitted: that only identifies atoms, which the assumed equality
     * justifies, and can only add arithmetic decisions.
     *
     * @param from the term whose occurrences would be rewritten
     * @param to the replacement term
     * @param services access to the integer theory operators
     * @return whether the rewrite keeps the arithmetic forms intact
     */
    @Override
    public boolean allowsEqualityRewrite(JTerm from, JTerm to, Services services) {
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        if (from.op() == integerLDT.getNumberSymbol()) {
            return false;
        }
        return !hasPolynomialStructure(from, integerLDT) && !hasPolynomialStructure(to, integerLDT);
    }

    /**
     * Whether the term's top operator is one the polynomial decomposition takes apart. Besides the
     * sum and product this covers difference and negation, which the proof search rewrites into
     * them.
     *
     * @param t a term
     * @param integerLDT the integer theory operators
     * @return whether the top operator carries polynomial structure
     */
    private static boolean hasPolynomialStructure(JTerm t, IntegerLDT integerLDT) {
        final Operator op = t.op();
        return op == integerLDT.getAdd() || op == integerLDT.getMul()
                || op == integerLDT.getSub() || op == integerLDT.getNeg();
    }
}
