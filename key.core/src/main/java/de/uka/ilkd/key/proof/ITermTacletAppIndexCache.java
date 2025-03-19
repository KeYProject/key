/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.logic.Term;

/**
 * The general interface for caches for accelerating <code>TermTacletAppIndex</code>.
 *
 * @see TermTacletAppIndexCacheSet
 */
public interface ITermTacletAppIndexCache {

    /**
     * @return the taclet app index for the term <code>t</code>, or <code>null</code> if no index
     *         for this term was found in the cache
     */
    TermTacletAppIndex getIndexForTerm(Term t);

    /**
     * Put the taclet app index <code>index</code> for the term <code>t</code> in the cache
     */
    void putIndexForTerm(Term t, TermTacletAppIndex index);

    /**
     * Determine the cache that is responsible for locations within the <code>subtermIndex</code>'th
     * subterm of the term <code>t</code> (assuming that <code>this</code> cache is responsible for
     * the location of the term <code>t</code>). This method is used in
     * <code>TermTacletAppIndex</code> when recursively constructing the index for a given term.
     */
    ITermTacletAppIndexCache descend(Term t, int subtermIndex);

}
