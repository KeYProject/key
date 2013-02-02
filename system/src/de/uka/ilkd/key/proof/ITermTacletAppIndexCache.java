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

import de.uka.ilkd.key.logic.Term;

/**
 * The general interface for caches for accelerating
 * <code>TermTacletAppIndex</code>.
 * 
 * @see TermTacletAppIndexCacheSet
 */
public interface ITermTacletAppIndexCache {
    
    /**
     * @return the taclet app index for the term <code>t</code>, or
     *         <code>null</code> if no index for this term was found in the
     *         cache
     */
    TermTacletAppIndex getIndexForTerm(Term t);

    /**
     * Put the taclet app index <code>index</code> for the term <code>t</code>
     * in the cache
     */
    void putIndexForTerm(Term t, TermTacletAppIndex index);

    /**
     * Determine the cache that is responsible for locations within the
     * <code>subtermIndex</code>'th subterm of the term <code>t</code>
     * (assuming that <code>this</code> cache is responsible for the location
     * of the term <code>t</code>). This method is used in
     * <code>TermTacletAppIndex</code> when recursively constructing the index
     * for a given term.
     */
    ITermTacletAppIndexCache descend(Term t, int subtermIndex);
    
}
