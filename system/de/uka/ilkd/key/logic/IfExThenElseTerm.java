// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.IfExThenElse;


/**
 *
 */
class IfExThenElseTerm extends Term {
  
    private final ArrayOfTerm subTerm;

    /** depth of the term */
    private final int depth;

    private final ArrayOfQuantifiableVariable exVariables;
    
    public IfExThenElseTerm (IfExThenElse op,
                             Term[] subs,
                             ArrayOfQuantifiableVariable exVariables) {
        super ( op, op.sort ( subs ) );

        this.exVariables = exVariables;
        this.subTerm = new ArrayOfTerm ( subs );
        
        int max_depth = -1;
        for ( int i = 0; i < subs.length; i++ ) {
            if ( subs[i].depth () > max_depth ) {
                max_depth = subs[i].depth ();
            }
        }
        depth = max_depth + 1;
    }
 
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.Term#varsBoundHere(int)
     */
    public ArrayOfQuantifiableVariable varsBoundHere (int n) {
        if ( n == 0 || n == 1 ) return exVariables;
        return new ArrayOfQuantifiableVariable ();
    }    

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.Term#arity()
     */
    public int arity () {
        return subTerm.size();
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.Term#depth()
     */
    public int depth () {
        return depth;
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.Term#sub(int)
     */
    public Term sub (int nr) {
        return subTerm.getTerm ( nr );
    }
}
