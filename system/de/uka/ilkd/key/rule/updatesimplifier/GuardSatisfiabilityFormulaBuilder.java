// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;


/**
 *
 */
public class GuardSatisfiabilityFormulaBuilder extends GuardSimplifier {

    public GuardSatisfiabilityFormulaBuilder (Term condition,
                                              ImmutableArray<QuantifiableVariable> arMinimizedVars) {
        super ( condition, arMinimizedVars );

        simplify ();
    }
    
    public Term createFormula () {
        if ( isValidGuard () || isUnsatisfiableGuard () || !bindsVariables () )
            return getCondition ();
        
        final UpdateSimplifierTermFactory utf = UpdateSimplifierTermFactory.DEFAULT;
        final TermFactory tf = utf.getBasicTermFactory ();
        
        final ImmutableArray<QuantifiableVariable> minimizedVars = getMinimizedVars ();
	return tf.createQuantifierTerm ( Op.EX,
                                         minimizedVars,
                                         getCondition () );
    }
}
