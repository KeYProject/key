// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.AbstractUpdateRule;
import de.uka.ilkd.key.rule.UpdateSimplifier;

/**
 * Abstract update simplification rule for access operators.
 * @author bubel
 */
public abstract class ApplyOnAccessTerm extends AbstractUpdateRule {
    
    /**
     * @param updateSimplifier
     */
    public ApplyOnAccessTerm(UpdateSimplifier updateSimplifier) {
        super(updateSimplifier);
    }

    protected static Term compareObjects (Term o1, Term o2) {
        // compare the objects only if the sorts are compatible; this is
        // probably inconsistent with the new typed first-order basis of
        // KeY, TODO /PR
        final UpdateSimplifierTermFactory utf = UpdateSimplifierTermFactory.DEFAULT;
        if ( o1.sort ().extendsTrans ( o2.sort () )
             || o2.sort ().extendsTrans ( o1.sort () ) )
            return utf.getBasicTermFactory ().createEqualityTerm ( o1, o2 );
        else
            return utf.getUnsatisfiableGuard ();
    }

}
