/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

import de.uka.ilkd.key.logic.Term;

/**
 * <p>
 * This interface is used for equality checks and hashing modulo a certain property on terms.
 * </p>
 * Objects of classes implementing this interface are given to the methods in
 * {@link TermEqualsModProperty} as parameters to unify equality checks and hashing modulo different
 * properties.
 *
 * @author Tobias Reinhold
 */
public interface TermProperty {
    /**
     * Checks <code>term</code> and <code>other</code> for equality ignoring a certain property.
     *
     * @param term the term to check for equality with <code>o</code>
     * @param o the object to check for equality with <code>term</code>
     * @return whether <code>term</code> and <code>o</code> are equal ignoring a certain property
     */
    Boolean equalsModThisProperty(Term term, Object o);

    /**
     * Computes the hash code of the <code>term</code>> in a context where
     * {@link this#equalsModThisProperty(Term, Object)} is used as an equality check, so that it can
     * be used in, e.g., a HashMap.
     *
     * @param term the term to compute the hash code for
     * @return the hash code of <code>term</code> ignoring a certain property
     */
    int hashCodeModThisProperty(Term term);
}
