// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.pp;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Sequent;


/**
 * Select the formulas of the sequent that should be printed, using
 * the user constraint
 */
@Deprecated
public class ConstraintSequentPrintFilter implements SequentPrintFilter {

    protected Sequent              originalSequent;

    protected ImmutableList<SequentPrintFilterEntry> antec = null;
    protected ImmutableList<SequentPrintFilterEntry> succ  = null;

    public ConstraintSequentPrintFilter ( Sequent    p_s ) {
	originalSequent = p_s;	
    }

    protected void filterSequent () {
	if ( antec != null )
	    return;

	Iterator<ConstrainedFormula> it;

	antec = ImmutableSLList.<SequentPrintFilterEntry>nil();
	it    = originalSequent.antecedent ().iterator ();
	while ( it.hasNext () )
	    antec = antec.append ( filterFormula ( it.next () ) );
	
	succ  = ImmutableSLList.<SequentPrintFilterEntry>nil();
	it    = originalSequent.succedent ().iterator ();
	while ( it.hasNext () )
	    succ  = succ .append ( filterFormula ( it.next () ) );
    }

    protected SequentPrintFilterEntry filterFormula ( ConstrainedFormula p_cfma ) {
	return new Entry ( p_cfma,
		p_cfma );
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


    protected static class Entry implements SequentPrintFilterEntry {
	final ConstrainedFormula filteredFormula;
	final ConstrainedFormula originalFormula;


	public Entry ( ConstrainedFormula p_filteredFormula,
		       ConstrainedFormula p_originalFormula ) {
	    filteredFormula   = p_filteredFormula;
	    originalFormula   = p_originalFormula;
	}

	/**
	 * Formula to display
	 */
	public ConstrainedFormula getFilteredFormula   () {
	    return filteredFormula;
	}

	/**
	 * Original formula from sequent
	 */
	public ConstrainedFormula getOriginalFormula   () {
	    return originalFormula;
	}

    }

}
