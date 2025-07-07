/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.instantiation;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.util.collection.ImmutableMap;

import org.jspecify.annotations.Nullable;

/// Implementations of this interface know which schema variables have been matched and their
/// respective instantiations.
public interface SVInstantiations {

    /// retrieves the schema variable of the specified name if it has already been instantiated,
    /// otherwise `null`
    /// is returned
    ///
    /// @param name Name of the schema variable
    /// @return the SchemaVariable
    SchemaVariable lookupVar(Name name);

    /// checks whether a schema variable of the specified name has been instantiated and
    /// returns its instantiation otherwise `null` is returned
    ///
    /// @param name Name of the schema variable
    /// @return the instantiation of the schema variable, `null` if no instantiation for a
    /// schema variable of the
    /// specified name is available
    <T> T lookupValue(Name name);

    /// checks whether the given schema variable has been instantiated and
    /// returns its instantiation otherwise `null` is returned
    ///
    /// @param sv the [SchemaVariable]
    /// @return the instantiation of the schema variable, `null` if no instantiation for the
    /// schema variable is
    /// available
    @Nullable
    <T> T getInstantiation(SchemaVariable sv);


    /// checks whether the given schema variable has been instantiated
    ///
    /// @param sv the [SchemaVariable]
    /// @return true if and only if an instantiation of the schema variable is available
    boolean isInstantiated(SchemaVariable sv);

    /// returns a map that contains all instantiated schema variables and their respective
    /// instantiation
    ///
    /// @return a map that contains all instantiated schema variables and their respective
    /// instantiation
    ImmutableMap<SchemaVariable, InstantiationEntry<?>> getInstantiationMap();

    ///
    /// returns a new [SVInstantiations] object that contains all instantiations contained in
    /// `this` and
    /// the `other` [SVInstantiations] object
    ///
    ///
    /// For performance reasons it is the responsibility of the caller to ensure that the union can
    /// be computed, e.g.
    /// to ensure that no schema variable is instantiated with different values
    ///
    ///
    /// Implementations might perform their own (partial) checks and throw a runtime exception if
    /// this assumption is violated.
    ///
    ///
    /// @param other the [SVInstantiations] with which to merge
    /// @param services the [LogicServices]
    /// @return the union of the instantiations
    SVInstantiations union(SVInstantiations other, LogicServices services);
}
