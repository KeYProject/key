/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.instantiation;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.proof.ProofServices;
import org.key_project.prover.rules.instantiation.caches.AssumesFormulaInstantiationCache;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableArray;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.checkerframework.checker.nullness.qual.Nullable;

/// Instantiation of an assumes-formula that is present as a formula of the proof goal's sequent.
///
/// This instantiation kind is used if the formula used as an instantiation for one of the
/// assumes-formulas
/// is syntactically present in the sequent. In that case the instantiation has not to be proven
/// to be valid as part of a separate proof goal.
///
///
/// @see AssumesFormulaInstantiation,AssumesFormulaInstDirect
public class AssumesFormulaInstSeq
        implements AssumesFormulaInstantiation {
    /// Sequent and formula
    private final Sequent seq;
    private final boolean inAntecedent; // formula is in antecedent?
    private final SequentFormula instantiation;

    public AssumesFormulaInstSeq(Sequent seq, boolean inAntecedent, SequentFormula instantiation) {
        this.seq = seq;
        this.inAntecedent = inAntecedent;
        this.instantiation = instantiation;
    }

    public AssumesFormulaInstSeq(Sequent instantiation, int indexPositionInSequent) {
        this(instantiation, instantiation.numberInAntecedent(indexPositionInSequent),
            instantiation.getFormulaByNr(indexPositionInSequent));
    }

    /// @return the cf this is pointing to
    @Override
    public SequentFormula getSequentFormula() {
        return instantiation;
    }

    /// Create a list with all formulas of a given semi-sequent
    private static ImmutableArray<AssumesFormulaInstantiation> createListHelp(Sequent p_s,
            Semisequent semi,
            boolean inAntecedent) {
        final AssumesFormulaInstSeq[] assumesInstFromSeq =
            new AssumesFormulaInstSeq[semi.size()];
        int i = assumesInstFromSeq.length - 1;

        for (final var sf : semi) {
            assumesInstFromSeq[i] = new AssumesFormulaInstSeq(p_s, inAntecedent, sf);
            --i;
        }

        return new ImmutableArray<>(assumesInstFromSeq);
    }

    /// Retrieves a list with all formulas of a given semi-sequent
    public static ImmutableArray<AssumesFormulaInstantiation> createList(Sequent p_s,
            boolean inAntecedent,
            ProofServices services) {
        final AssumesFormulaInstantiationCache cache =
            services.getCaches().getAssumesFormulaInstantiationCache();
        final Semisequent semi = inAntecedent ? p_s.antecedent() : p_s.succedent();

        ImmutableArray<AssumesFormulaInstantiation> val = cache.get(inAntecedent, semi);

        if (val == null) {
            val = createListHelp(p_s, semi, inAntecedent);
            cache.put(inAntecedent, semi, val);
        }

        return val;
    }

    @Override
    public String toString() {
        return instantiation.formula().toString();
    }

    @Override
    public boolean equals(@Nullable Object p_obj) {
        if (!(p_obj instanceof AssumesFormulaInstSeq other)) {
            return false;
        }
        return seq == other.seq && instantiation == other.instantiation
                && inAntecedent == other.inAntecedent;
    }

    @Override
    public int hashCode() {
        int result = 17;
        result = 37 * result + seq.hashCode();
        result = 37 * result + instantiation.hashCode();
        result = 37 * result + (inAntecedent ? 0 : 1);
        return result;
    }

    public boolean inAntecedent() {
        return inAntecedent;
    }

    private volatile @MonotonicNonNull PosInOccurrence pioCache = null;

    public PosInOccurrence toPosInOccurrence() {
        if (pioCache == null) {
            pioCache = new PosInOccurrence(instantiation, PosInTerm.getTopLevel(), inAntecedent);
        }
        return pioCache;
    }
}
