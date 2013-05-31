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


package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.Iterator;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

class MultiTrigger implements Trigger {

    private final ImmutableSet<Trigger> triggers;

    private final ImmutableSet<QuantifiableVariable> qvs;

    private final Term clause;

    MultiTrigger(ImmutableSet<Trigger> triggers, ImmutableSet<QuantifiableVariable> qvs,
	    Term clause) {
	this.triggers = triggers;
	this.qvs = qvs;
	this.clause = clause;
    }

    public ImmutableSet<Substitution> getSubstitutionsFromTerms(
	    ImmutableSet<Term> targetTerms, Services services) {
	ImmutableSet<Substitution> res = DefaultImmutableSet.<Substitution> nil();
	
	ImmutableSet<Substitution> mulsubs = setMultiSubstitution(triggers.iterator(),
		targetTerms, services);

	for (Substitution sub : mulsubs) {
	    if (sub.isTotalOn(qvs)) {
		res = res.add(sub);
	    }
	}

	return res;
    }

    /** help function for getMultiSubstitution */
    private ImmutableSet<Substitution> setMultiSubstitution(
	    Iterator<? extends Trigger> ts, ImmutableSet<Term> terms, Services services) {
	ImmutableSet<Substitution> res = DefaultImmutableSet.<Substitution> nil();
	if (ts.hasNext()) {
	    ImmutableSet<Substitution> subi = ts.next().getSubstitutionsFromTerms(
		    terms, services);
	    ImmutableSet<Substitution> nextSubs = setMultiSubstitution(ts, terms,
		    services);
	    if (nextSubs.isEmpty()) {
		return subi;
	    } else if (subi.isEmpty()) {
		return nextSubs;
	    }
	    for (Substitution sub0 : nextSubs) {
		for (Substitution subiSub : subi) {
		    final Substitution sub1 = unifySubstitution(sub0, subiSub);
		    if (sub1 != null) {
			res = res.add(sub1);
		    }
		}

	    }
	}
	return res;
    }

    /**
     * unify two substitution, if same variable are bound with same term return
     * a new substitution with all universal quantifiable variables in two
     * substituition, otherwise return null
     */
    private Substitution unifySubstitution(Substitution sub0, Substitution sub1) {
	Iterator<ImmutableMapEntry<QuantifiableVariable, Term>> it0 = sub0.getVarMap()
		.entryIterator();
	final ImmutableMap<QuantifiableVariable, Term> varMap1 = sub1.getVarMap();
	ImmutableMap<QuantifiableVariable, Term> resMap = varMap1;

	while (it0.hasNext()) {
	    ImmutableMapEntry<QuantifiableVariable, Term> en = it0.next();
	    QuantifiableVariable key = en.key();
	    Term value = en.value();
	    if (varMap1.containsKey(key)) {
		if (!(varMap1.get(key).equals(value)))
		    return null;
	    }
	    resMap = resMap.put(key, value);
	}
	return new Substitution(resMap);
    }

    public boolean equals(Object arg0) {
	if (!(arg0 instanceof MultiTrigger))
	    return false;

	final MultiTrigger a = (MultiTrigger) arg0;
	return a.triggers.equals(triggers);
    }

    public int hashCode() {
	return triggers.hashCode();
    }

    public String toString() {
	return "" + triggers;
    }

    public Term getTriggerTerm() {
	return clause;
    }

}
