// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
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
        
        final ImmutableList<IfFormulaInstantiation> insts = app.ifFormulaInstantiations ();
        if ( insts == null ) return c;

        //      TODO: c will be unsatifiable if intersection sorts are required
        // (is this intended)? or rather new Namespace() 
        for (IfFormulaInstantiation inst : insts) c = c.join(inst.getConstrainedFormula().constraint(), services);
        return c;
    }
    
}
