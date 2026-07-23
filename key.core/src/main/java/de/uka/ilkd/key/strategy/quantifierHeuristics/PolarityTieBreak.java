/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

/**
 * Orders tied instantiation candidates by their proving-polarity connection to the sequent (see
 * {@link PolarityOccurrenceTieBreak#polarityValue}). The tie-break of the {@code Best} quantifier
 * treatment.
 */
final class PolarityTieBreak extends PolarityOccurrenceTieBreak {

    static final PolarityTieBreak INSTANCE = new PolarityTieBreak();

    private PolarityTieBreak() {
    }

    @Override
    public Scorer prepare(View view) {
        final OccData d = computeOccData(view);
        return inst -> polarityValue(d, inst);
    }
}
