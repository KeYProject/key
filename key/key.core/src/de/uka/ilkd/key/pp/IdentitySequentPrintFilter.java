// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.pp;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;


/**
 * Identity Filter not doing anything 
 */
public class IdentitySequentPrintFilter extends SequentPrintFilter {

    protected void filterSequent () {
		if ( antec != null )
		    return;
		filterIdentity();
    }

    protected SequentPrintFilterEntry filterFormula ( SequentFormula p_cfma ) {
    	return new IdentityFilterEntry ( p_cfma );
    }

    /**
     * Get the formulas of the filtered sequent and the constraints to
     * use for instantiating metavariables when printing
     */
    public ImmutableList<SequentPrintFilterEntry> getFilteredAntec       () {
    	filterSequent();
    	return antec;
    }

    public ImmutableList<SequentPrintFilterEntry> getFilteredSucc        () {
		filterSequent();
		return succ;
    }


    public static class IdentityFilterEntry implements SequentPrintFilterEntry {
    	final SequentFormula originalFormula;

		public IdentityFilterEntry ( SequentFormula p_originalFormula) {
		    originalFormula   = p_originalFormula;
		}

		/**
		 * Formula to display
		 */
		public SequentFormula getFilteredFormula   () {
		    return originalFormula;
		}
	
		/**
		 * Original formula from sequent
		 */
		public SequentFormula getOriginalFormula   () {
		    return originalFormula;
		}

    }
}