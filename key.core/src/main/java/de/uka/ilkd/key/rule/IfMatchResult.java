/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;


import de.uka.ilkd.key.util.Debug;

import org.key_project.util.collection.ImmutableList;


public class IfMatchResult {

    /**
     * List of matching formulas and list of corresponding match conditions.
     */
    private final ImmutableList<IfFormulaInstantiation> candidates;
    private final ImmutableList<MatchConditions> mcCandidates;

    /**
     * PRECONDITION: p_candidates.size () == p_mcCandidates.size ()
     */
    public IfMatchResult(ImmutableList<IfFormulaInstantiation> p_candidates,
            ImmutableList<MatchConditions> p_mcCandidates) {
        Debug.assertTrue(p_candidates.size() == p_mcCandidates.size(),
            "Size of arguments must be equal");
        candidates = p_candidates;
        mcCandidates = p_mcCandidates;
    }

    public ImmutableList<IfFormulaInstantiation> getFormulas() {
        return candidates;
    }

    public ImmutableList<MatchConditions> getMatchConditions() {
        return mcCandidates;
    }

}
