/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;

/// Named cost constants used to define the application order of sequence rules within the
/// [SeqStrategy]
final class SeqCost {
    private SeqCost() {}

    /// Cost used to ensure that sequences like `seqDef{u}(l, h, seqGet(s, u))` are expanded first,
    /// before `seqDefOfSeq` gets applied, the latter of which causes splitting.
    static final long EXPAND_BEFORE_SEQDEF_SPLIT = -2100;

    /// Used for rules that add direct consequences of axioms once per formula or term, like
    /// `seqLen(s) >= 0`
    static final long AXIOM_LIKE = -500;

    /// some cost between default and [org.key_project.prover.strategy.costbased.CostBand#DEFER]
    static final long DEFER_SLIGHTLY = 100;
}
