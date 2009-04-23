// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.logic.Sequent;


/**
 * Filter a given sequent to prepare it for the SequentPrinter class
 * by adjusting constraints, deleting formulas, etc.
 */
public interface SequentPrintFilter {

    /**
     * @return the original sequent
     */
    Sequent            getSequent                ();

    /**
     * Get the formulas of the filtered sequent and the constraints to
     * use for instantiating metavariables when printing
     */
    ListOfSequentPrintFilterEntry getAntec       ();

    ListOfSequentPrintFilterEntry getSucc        ();
    
}
