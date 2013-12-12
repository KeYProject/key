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



package de.uka.ilkd.key.logic;

import java.util.*;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.util.LRUCache;

/** 
 * The TermFactory is the <em>only</em> way to create terms using constructors 
 * of class Term or any of its subclasses. It is the only class that implements 
 * and may exploit knowledge about sub classes of {@link Term}. All other 
 * classes of the system only know about terms what the {@link Term} class 
 * offers them. 
 * 
 * This class is used to encapsulate knowledge about the internal term 
 * structures.
 * See {@link de.uka.ilkd.key.logic.TermBuilder} for more convenient methods to 
 * create terms. 
 */
public final class TermFactory {
    
    /** 
     * The only instance of TermFactory. 
     */
    public static final TermFactory DEFAULT = new TermFactory();    

    private static final Map<Term, Term> cache 
    	= Collections.synchronizedMap(new LRUCache<Term, Term>(20000));

    private static final ImmutableArray<Term> NO_SUBTERMS = new ImmutableArray<Term>();
    

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    private TermFactory() {
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    /**
     * Master method for term creation. Should be the only place where terms 
     * are created in the entire system.
     */
    public Term createTerm(Operator op, 
	    		   ImmutableArray<Term> subs, 
	    		   ImmutableArray<QuantifiableVariable> boundVars,
	    		   JavaBlock javaBlock,
			   ImmutableArray<TermLabel> labels) {
	if(op == null) {
	    throw new TermCreationException("null-Operator at TermFactory");
	}
	
	final Term newTerm 
		= (labels == null || labels.isEmpty() ? 
				new TermImpl(op, subs, boundVars, javaBlock) : 
			new LabeledTermImpl(op, subs, boundVars, javaBlock, labels)).checked();
	// Check if caching is possible. It is not possible if a non empty JavaBlock is available
	// in the term or in one of its children because the meta information like PositionInfos
	// may be different.
	if (!newTerm.isContainsJavaBlockRecursive()) {
	   Term term = cache.get(newTerm);
	   if(term == null) {
	       term = newTerm;
	       cache.put(term, term);
	   }
	   return term;
	}
	else {
	   return newTerm;
	}
    } 
    
    
    public Term createTerm(Operator op, 
	    		   ImmutableArray<Term> subs, 
	    		   ImmutableArray<QuantifiableVariable> boundVars,
	    		   JavaBlock javaBlock) {

    	return createTerm(op, subs, boundVars, javaBlock, null);
    }


    public Term createTerm(Operator op,
                           Term[] subs,
                           ImmutableArray<QuantifiableVariable> boundVars,
                           JavaBlock javaBlock,
                           TermLabel label) {
        return createTerm(op, new ImmutableArray<Term>(subs), boundVars,
                          javaBlock, new ImmutableArray<TermLabel>(label));
    }


    public Term createTerm(Operator op,
                           Term[] subs,
	    		   ImmutableArray<QuantifiableVariable> boundVars,
	    		   JavaBlock javaBlock) {
	return createTerm(op, new ImmutableArray<Term>(subs), boundVars, javaBlock, null);
    }


    public Term createTerm(Operator op, Term[] subs, TermLabel label) {
        return createTerm(op, subs, null, null, label);
    }
    
    
    public Term createTerm(Operator op, Term[] subs) {
	return createTerm(op, subs, null, null);
    }
    
    
    public Term createTerm(Operator op, Term sub) {
	return createTerm(op, new ImmutableArray<Term>(sub), null, null);
    }    
    
    
    public Term createTerm(Operator op, Term sub1, Term sub2) {
	return createTerm(op, new Term[]{sub1, sub2}, null, null);
    }    
    
    
    public Term createTerm(Operator op) {
	return createTerm(op, NO_SUBTERMS, null, null);
    }

    
    public Term createTerm(Operator op,
                           Term[] subs,
                           ImmutableArray<QuantifiableVariable> boundVars,
                           JavaBlock javaBlock,
                           ImmutableArray<TermLabel> labels) {
    	return createTerm(op, new ImmutableArray<Term>(subs), boundVars, javaBlock, labels);
    }


    public Term createTerm(Operator op, Term[] subs, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, subs, null, null, labels);
    }


    public Term createTerm(Operator op, Term sub, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, new ImmutableArray<Term>(sub), null, null, labels);
    }    


    public Term createTerm(Operator op, Term sub1, Term sub2, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, new Term[]{sub1, sub2}, null, null, labels);
    }    


    public Term createTerm(Operator op, ImmutableArray<TermLabel> labels) {
    	return createTerm(op, NO_SUBTERMS, null, null, labels);
    }

}
