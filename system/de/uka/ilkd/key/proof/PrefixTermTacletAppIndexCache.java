// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.ListOfQuantifiableVariable;

/**
 * The abstract superclass of caches for taclet app indexes that are separated
 * by different prefixes of bound variables. This class simply stores a
 * <code>ListOfQuantifiableVariable</code> and offers a couple of access
 * functions to this list.
 */
abstract class PrefixTermTacletAppIndexCache implements
                                             ITermTacletAppIndexCache {

    private final ListOfQuantifiableVariable prefix;   
    
    protected PrefixTermTacletAppIndexCache(ListOfQuantifiableVariable prefix) {
        this.prefix = prefix;
    }

    protected ListOfQuantifiableVariable getPrefix() {
        return prefix;
    }

    protected ListOfQuantifiableVariable
              getExtendedPrefix(ArrayOfQuantifiableVariable extension) {
        ListOfQuantifiableVariable res = prefix;
        for ( int i = 0; i != extension.size (); ++i )
            res = res.prepend ( extension.getQuantifiableVariable ( i ) );
        return res;
    }

    protected ListOfQuantifiableVariable getExtendedPrefix(Term t, int subtermIndex) {
        return getExtendedPrefix ( t.varsBoundHere ( subtermIndex ) );
    }
    
}
