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
import de.uka.ilkd.key.logic.op.QuantifiableVariable;


class IfExCascadeEntryBuilder extends GuardSimplifier {
    
    private Term thenBranch;
    
    public IfExCascadeEntryBuilder (final Term condition,
                           final ArrayOfQuantifiableVariable minimizedVars,
                           final Term thenBranch) {
        super ( condition, minimizedVars );
        this.thenBranch = thenBranch;
        
        simplify ();
    }

    protected boolean isNeededVar (QuantifiableVariable var) {
        return thenBranch.freeVars ().contains ( var );
    }

    protected void substitute (QuantifiableVariable var, Term substTerm) {
        thenBranch = subst ( var, substTerm, thenBranch );
    }

    public Term createTerm (Term elseBranch) {
        if ( isValidGuard () && !bindsVariables ()
             || thenBranch.equalsModRenaming ( elseBranch ) ) {
            return thenBranch;
        } else if ( isUnsatisfiableGuard() ) {
            return elseBranch;
        } else if ( bindsVariables() ) {
            final ArrayOfQuantifiableVariable vars =
                new ArrayOfQuantifiableVariable ( getMinimizedVars().toArray () );
            return TermFactory.DEFAULT.createIfExThenElseTerm ( vars,
                                                                getCondition(),
                                                                thenBranch,
                                                                elseBranch );
        } else {
            return TermFactory.DEFAULT.createIfThenElseTerm ( getCondition(),
                                                              thenBranch,
                                                              elseBranch );                
        }
    }

    public boolean isAlwaysElse () {
        return isUnsatisfiableGuard ();
    }

    public boolean isEndOfCascade () {
        return isValidGuard () && !bindsVariables ();
    }
}
