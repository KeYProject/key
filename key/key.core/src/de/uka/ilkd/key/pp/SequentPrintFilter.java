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

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Sequent;


/**
 * Filter a given sequent to prepare it for the SequentPrinter class
 * by adjusting constraints, deleting formulas, etc.
 */
public abstract class SequentPrintFilter {
	
	protected Sequent originalSequent;

    protected ImmutableList<SequentPrintFilterEntry> antec;
    protected ImmutableList<SequentPrintFilterEntry> succ;
    
    /**
     * @return the original sequent
     */
    public Sequent getOriginalSequent() {
    	return originalSequent;
    }
    
    protected abstract void filterSequent();
    
    /**
     * sets the (original) sequent of this filter
     */
    public void setSequent(Sequent s) {
    	originalSequent = s;
    	antec = null;
    	succ = null;
    }

    /**
     * Get the formulas of the filtered sequent and the constraints to
     * use for instantiating metavariables when printing
     */
    public ImmutableList<SequentPrintFilterEntry> getFilteredAntec() {
    	if (antec == null) {
    		filterSequent();
    	}
    	return antec;
    }
    public ImmutableList<SequentPrintFilterEntry> getFilteredSucc() {
    	if (succ == null) {
    		filterSequent();
    	}
    	return succ;
    }
}