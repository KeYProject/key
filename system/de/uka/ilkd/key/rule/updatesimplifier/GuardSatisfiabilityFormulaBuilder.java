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
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;


/**
 *
 */
public class GuardSatisfiabilityFormulaBuilder extends GuardSimplifier {

    public GuardSatisfiabilityFormulaBuilder (Term condition,
                                              ArrayOfQuantifiableVariable arMinimizedVars) {
        super ( condition, arMinimizedVars );

        simplify ();
    }
    
    public Term createFormula () {
        if ( isValidGuard () || isUnsatisfiableGuard () || !bindsVariables () )
            return getCondition ();
        
        final UpdateSimplifierTermFactory utf = UpdateSimplifierTermFactory.DEFAULT;
        final TermFactory tf = utf.getBasicTermFactory ();
        
        return tf.createQuantifierTerm ( Quantifier.EX,
                                         getMinimizedVars ().toArray (),
                                         getCondition () );
    }
}
