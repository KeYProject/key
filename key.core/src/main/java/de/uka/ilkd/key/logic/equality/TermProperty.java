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
     * Checks {@code term1} and {@code term2} for equality ignoring a certain property.
     *
     * @param term1 the first term to check for equality with {@code term2}
     * @param term2 the second term to check for equality with {@code term1}
     * @return whether {@code term1} and {@code term2} are equal ignoring a certain property
     */
    Boolean equalsModThisProperty(Term term1, Term term2);

    /**
     * Computes the hash code of the {@code term} in a context where
     * {@link this#equalsModThisProperty(Term, Term)} is used as an equality check, so that it can
     * be used in, e.g., a HashMap.
     *
     * @param term the term to compute the hash code for
     * @return the hash code of {@code term} ignoring a certain property
     */
    int hashCodeModThisProperty(Term term);
}
