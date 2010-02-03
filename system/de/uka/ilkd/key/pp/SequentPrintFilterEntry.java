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

import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Constraint;


/**
 * One element of a sequent as delivered by SequentPrintFilter
 */

public interface SequentPrintFilterEntry {

    /**
     * Formula to display
     */
    ConstrainedFormula getFilteredFormula   ();

    /**
     * Original formula from sequent
     */
    ConstrainedFormula getOriginalFormula   ();

    /**
     * Constraint for metavariable instantiations
     */
    Constraint         getDisplayConstraint ();

}
