package de.uka.ilkd.key.rule;


import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.util.Debug;


public class IfMatchResult {

    /**
     * List of matching formulas and list of corresponding match conditions.
     */
    private ImmutableList<IfFormulaInstantiation> candidates;
    private ImmutableList<MatchConditions> mcCandidates;

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
