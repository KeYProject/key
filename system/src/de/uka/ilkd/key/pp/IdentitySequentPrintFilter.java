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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Sequent;


/**
 * Identity Filter not doing anything 
 */
public class IdentitySequentPrintFilter implements SequentPrintFilter {

    protected Sequent              originalSequent;

    protected ImmutableList<SequentPrintFilterEntry> antec = null;
    protected ImmutableList<SequentPrintFilterEntry> succ  = null;

    public IdentitySequentPrintFilter ( Sequent    p_s ) {
	originalSequent = p_s;	
    }

    protected void filterSequent () {
	if ( antec != null )
	    return;

	Iterator<SequentFormula> it;

	antec = ImmutableSLList.<SequentPrintFilterEntry>nil();
	it    = originalSequent.antecedent ().iterator ();
	while ( it.hasNext () )
	    antec = antec.append ( filterFormula ( it.next () ) );
	
	succ  = ImmutableSLList.<SequentPrintFilterEntry>nil();
	it    = originalSequent.succedent ().iterator ();
	while ( it.hasNext () )
	    succ  = succ .append ( filterFormula ( it.next () ) );
    }

    protected SequentPrintFilterEntry filterFormula ( SequentFormula p_cfma ) {
	return new IdentityFilterEntry ( p_cfma );
    }


    /**
     * @return the original sequent
     */
    public Sequent      getSequent         () {
	return originalSequent;
    }

    /**
     * Get the formulas of the filtered sequent and the constraints to
     * use for instantiating metavariables when printing
     */
    public ImmutableList<SequentPrintFilterEntry> getAntec       () {
	filterSequent ();
	return antec;
    }

    public ImmutableList<SequentPrintFilterEntry> getSucc        () {
	filterSequent ();
	return succ;
    }


    private static class IdentityFilterEntry implements SequentPrintFilterEntry {
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