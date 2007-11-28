// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.rule.IteratorOfIfFormulaInstantiation;
import de.uka.ilkd.key.rule.ListOfIfFormulaInstantiation;
import de.uka.ilkd.key.rule.TacletApp;


/**
 * Abstract superclass for the features treating constraints; contains some
 * generally useful methods
 */
public abstract class AbstractConstraintStrengthenFeature extends
                                                BinaryTacletAppFeature {

    protected AbstractConstraintStrengthenFeature() {
        super ( false );
    }
    
    /**
     * @preconditions app.ifInstsComplete ()
     * @param services TODO
     * @return the conjunction of the constraints that are attached to formulas
     *         matched by the if-clauses of the taclet
     */
    protected static Constraint getIfConstraint (TacletApp app, Services services) {
        Constraint c = Constraint.BOTTOM;
        
        final ListOfIfFormulaInstantiation insts = app.ifFormulaInstantiations ();
        if ( insts == null ) return c;
        
        final IteratorOfIfFormulaInstantiation it = insts.iterator ();
        //      TODO: c will be unsatifiable if intersection sorts are required 
        // (is this intended)? or rather new Namespace() 
        while ( it.hasNext () )
            c = c.join ( it.next ().getConstrainedFormula ().constraint (), services );
        return c;
    }
    
}
