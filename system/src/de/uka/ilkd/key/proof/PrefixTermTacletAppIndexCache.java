// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

/**
 * The abstract superclass of caches for taclet app indexes that are separated
 * by different prefixes of bound variables. This class simply stores a
 * <code>IList<QuantifiableVariable></code> and offers a couple of access
 * functions to this list.
 */
abstract class PrefixTermTacletAppIndexCache implements
                                             ITermTacletAppIndexCache {

    private final ImmutableList<QuantifiableVariable> prefix;   
    
    protected PrefixTermTacletAppIndexCache(ImmutableList<QuantifiableVariable> prefix) {
        this.prefix = prefix;
    }

    protected ImmutableList<QuantifiableVariable> getPrefix() {
        return prefix;
    }

    protected ImmutableList<QuantifiableVariable>
              getExtendedPrefix(ImmutableArray<QuantifiableVariable> extension) {
        ImmutableList<QuantifiableVariable> res = prefix;
        for ( int i = 0; i != extension.size (); ++i )
            res = res.prepend ( extension.get ( i ) );
        return res;
    }

    protected ImmutableList<QuantifiableVariable> getExtendedPrefix(Term t, int subtermIndex) {
        return getExtendedPrefix ( t.varsBoundHere ( subtermIndex ) );
    }
    
}
