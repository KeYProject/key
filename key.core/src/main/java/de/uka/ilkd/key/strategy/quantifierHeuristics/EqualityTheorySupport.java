/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;

import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableSet;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;

/**
 * Support for the equality theory.
 *
 * Rejects the equality {@code =} as a trigger (matching on it has not been observed to help
 * instantiation) and provides no derived triggers. For cost prediction it decides a literal that is
 * an equality or equivalence whose two sides are equal up to renaming, and decides an arbitrary
 * literal that equals an assumed one up to renaming (or contradicts it under a negation).
 */
final class EqualityTheorySupport implements QuantifierTheorySupport {

    /**
     * Rejects the equality {@code =} as a trigger.
     *
     * @param candidate a trigger candidate that contains the quantified variables
     * @param services access to the theory operators
     * @return whether the candidate is rejected
     */
    @Override
    public boolean rejectsAsTrigger(JTerm candidate, Services services) {
        return candidate.op() == Equality.EQUALS;
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
            ImmutableSet<QuantifiableVariable> clauseVariables, Services services) {
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
}
