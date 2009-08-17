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
