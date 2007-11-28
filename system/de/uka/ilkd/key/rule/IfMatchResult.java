// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;


import de.uka.ilkd.key.util.Debug;


public class IfMatchResult {

    /**
     * List of matching formulas and list of corresponding match
     * conditions.
     */
    private ListOfIfFormulaInstantiation candidates;
    private ListOfMatchConditions        mcCandidates;

    /**
     * PRECONDITION: p_candidates.size () == p_mcCandidates.size ()
     */
    public IfMatchResult ( ListOfIfFormulaInstantiation p_candidates,
			   ListOfMatchConditions        p_mcCandidates ) {
	Debug.assertTrue ( p_candidates.size () == p_mcCandidates.size (),
			   "Size of arguments must be equal" );
	candidates   = p_candidates;
	mcCandidates = p_mcCandidates;
    }

    public ListOfIfFormulaInstantiation getFormulas () {
	return candidates;
    }

    public ListOfMatchConditions        getMatchConditions () {
	return mcCandidates;
    }

}
