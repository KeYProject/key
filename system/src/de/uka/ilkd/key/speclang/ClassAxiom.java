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


package de.uka.ilkd.key.speclang;


import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.Pair;


/**
 * An axiom originating from a (JML) specification, belonging to a particular
 * class, and constraining a particular observer symbol. A class axiom always
 * has an associated visibility. The visibility determines in which proofs the 
 * axiom is available, in accordance with the visibility rules of Java. If 
 * visible, it is made available not as a formula, but as one or many taclets 
 * (for performance reasons).
 */
public abstract class ClassAxiom implements SpecificationElement {
        

    protected static final TermBuilder TB = TermBuilder.DF;
    protected String displayName;
    
    /**
     * Returns the axiomatised function symbol. 
     */
    public abstract IObserverFunction getTarget();
 
    
    /**
     * Returns the pairs (kjt, obs) for which there is an occurrence of
     * o.obs in the axiom, where kjt is the type of o (excluding the
     * defining occurrence of the axiom target). 
     */
    public abstract ImmutableSet<Pair<Sort, IObserverFunction>> getUsedObservers(
	    						Services services);
    
    /**
     * The axiom as one or many taclets, where the non-defining occurrences of
     * the passed observers are replaced by their "limited" counterparts.
     */
    public abstract ImmutableSet<Taclet> getTaclets(
	    		ImmutableSet<Pair<Sort, IObserverFunction>> toLimit,
	    		Services services);    

    @Override
    public String getDisplayName() {
        return displayName == null ? getName() : displayName;
    }
}
