// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.rule;


import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.util.Debug;


public class IfMatchResult {

    /**
     * List of matching formulas and list of corresponding match
     * conditions.
     */
    private ImmutableList<IfFormulaInstantiation> candidates;
    private ImmutableList<MatchConditions>        mcCandidates;

    /**
     * PRECONDITION: p_candidates.size () == p_mcCandidates.size ()
     */
    public IfMatchResult ( ImmutableList<IfFormulaInstantiation> p_candidates,
			   ImmutableList<MatchConditions>        p_mcCandidates ) {
	Debug.assertTrue ( p_candidates.size () == p_mcCandidates.size (),
			   "Size of arguments must be equal" );
	candidates   = p_candidates;
	mcCandidates = p_mcCandidates;
    }

    public ImmutableList<IfFormulaInstantiation> getFormulas () {
	return candidates;
    }

    public ImmutableList<MatchConditions>        getMatchConditions () {
	return mcCandidates;
    }

}
