// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;

public class LoopPredicateSet {

    private final ImmutableSet<Term> replace;

    public LoopPredicateSet(ImmutableSet<Term> replace) {
	assert replace != null;
	this.replace = replace;
    }

    public ImmutableSet<Term> asSet() {
	// TODO Auto-generated method stub
	return replace;
    }

    public Term[] toArray() {
	return replace.toArray(new Term[replace.size()]);
    }

}
