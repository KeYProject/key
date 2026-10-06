/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics.theory;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.JTerm;

import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableSet;

/**
 * Support for the sequence theory: a sequence read with a compound index is registered as a
 * trigger together with its index.
 *
 * Trigger selection registers the smallest subterm that contains the quantified variables of the
 * clause. For {@code seqGet(s, k + t)} with quantified {@code t} this is the sum {@code k + t}.
 * The sum matches every sum of that shape on the sequent and does not determine the sequence
 * {@code s}. The read determines {@code s}. This support therefore registers the read as well.
 * Matching the read against {@code seqGet(s, x)} fails at the index, and the integer theory
 * solves {@code k + t = x} for {@code t} there (see {@link TheoryReasoning#solveForVariable}).
 *
 * Compound indices are the normal case for sequences. The rules for subsequence, concatenation
 * and reversal rewrite a read into a read of the underlying sequence at {@code idx + from},
 * {@code idx - seqLen(first)} and {@code seqLen(seq) - 1 - idx}.
 *
 * This support provides no derived triggers and decides no literals.
 */
final class SequenceTheorySupport implements QuantifierTheorySupport {

    /**
     * A candidate in the index position of a sequence read is {@code PREFER_ENCLOSING}: it
     * becomes a trigger, and the search continues with the read. Every other candidate is
     * {@code ACCEPTABLE}.
     *
     * A bare variable is never a candidate, so for a read with a variable as index the read
     * itself is the smallest candidate. A candidate in the sequence position, for example a
     * subsequence term, determines the sequence itself.
     *
     * @param candidate a trigger candidate that contains the quantified variables
     * @param enclosing the term the candidate is an argument of, null at the top of a literal
     * @param services access to the sequence theory operators
     * @return the verdict
     */
    @Override
    public CandidateVerdict verdictOn(JTerm candidate, JTerm enclosing, Services services) {
        final SeqLDT seqLDT = services.getTypeConverter().getSeqLDT();
        // the index is the second argument of seqGet
        if (enclosing != null && seqLDT.isSeqGetOp(enclosing.op())
                && enclosing.sub(1) == candidate) {
            return CandidateVerdict.PREFER_ENCLOSING;
        }
        return CandidateVerdict.ACCEPTABLE;
    }

    /**
     * Provides no derived triggers.
     *
     * @param term an accepted trigger term
     * @param clauseVariables the quantified variables of the clause the trigger belongs to
     * @param services access to the sequence theory operators
     * @return the empty list
     */
    @Override
    public List<JTerm> provideTriggers(JTerm term,
            ImmutableSet<QuantifiableVariable> clauseVariables, Services services,
            MetavariableFactory metavariableFactory) {
        return List.of();
    }
}
