/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

///
/// This interface is used for equality checks and hashing modulo a certain property.
///
/// Objects of classes implementing this interface are given to the methods in
/// [Property] as parameters to unify equality checks and hashing modulo different
/// properties.
///
/// @param <T> the type of the objects that are checked for equality or hashed
///
/// @author Tobias Reinhold
public interface Property<T> {
    /// Checks `t1` and `t2` for equality ignoring a certain property.
    ///
    /// @param t1 the first element of the equality check
    /// @param t2 the second element of the equality check
    /// @param v the additional arguments needed for the equality check
    /// @return whether `t1` and `t2` are equal ignoring a certain property
    /// @param <V> the type of the additional parameters needed for the comparison
    <V> boolean equalsModThisProperty(T t1, T t2, V... v);

    /// Computes the hash code of `t` in a context where
    /// [#equalsModThisProperty(Object,Object,Object[])]
    /// is used as an equality check, so that it can be used in, e.g., a HashMap.
    ///
    /// @param t the object to compute the hash code for
    /// @return the hash code of `t` ignoring a certain property
    int hashCodeModThisProperty(T t);
}
