/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

import org.key_project.logic.Property;

/**
 * Interface to check for equality ignoring given properties and to compute according hash codes.
 * <p>
 * Overview of currently implemented properties that can be used with this interface:
 * <l>
 * <li>For Terms:</li>
 * <ol>
 * <li>{@link RenamingTermProperty}: Terms are checked for equality modulo renaming.</li>
 * <li>{@link TermLabelsProperty}: Terms are checked for equality ignoring all term labels.</li>
 * <li>{@link IrrelevantTermLabelsProperty}: Terms are checked for equality ignoring irrelevant term
 * labels.</li>
 * <li>{@link ProofIrrelevancyProperty}: Terms are checked for equality ignoring proof irrelevant
 * attributes.</li>
 * </ol>
 * <li>For SourceElements:</li>
 * <ol>
 * <li>{@link RenamingSourceElementProperty}: Source elements are checked for equality modulo
 * renaming.</li>
 * </ol>
 * </l>
 *
 * @param <T> the type of the objects that are checked for equality or hashed
 *
 * @author Tobias Reinhold
 */
public interface EqualsModProperty<T> {

    /**
     * Checks whether this object is equal to {@code o} modulo the property described by
     * {@code property}.
     * <p>
     * Some properties call for additional arguments. For more information on that,
     * see the documentation of {@code equalsModThisProperty} for the certain property.
     * <p>
     * To get an overview of the currently implemented properties, see the documentation of
     * {@link EqualsModProperty}.
     *
     * @param o the object that is checked for equality
     * @param property the property to be ignored in the equality check
     * @param v the additional arguments needed by {@code property} for the equality check
     * @return whether this object is equal to <code>o</code>
     * @param <V> the type of the additional parameters needed by {@code property} for the
     *        comparison
     */
    <V> boolean equalsModProperty(Object o, Property<T> property, V... v);

    /**
     * Computes the hash code according to the given ignored {@code property}.
     *
     * @param property the ignored property according to which the hash code is computed
     * @return the hash code of this object
     */
    int hashCodeModProperty(Property<? super T> property);
}
