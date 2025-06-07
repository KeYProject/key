/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.instantiation;

import org.key_project.util.collection.ImmutableArray;

/// This class is used to store the instantiation of a SchemaVariable if it is a ProgramElement.
public class ListInstantiation<T> extends InstantiationEntry<ImmutableArray<T>> {

    /// type of the stored elements
    private final Class<T> type;

    /// creates a new ContextInstantiationEntry
    ///
    /// @param pes the ProgramElement array the SchemaVariable is instantiated with
    public ListInstantiation(ImmutableArray<T> pes, Class<T> type) {
        super(pes);
        this.type = type;
    }

    /// {@inheritDoc}
    @Override
    public ImmutableArray<T> getInstantiation() {
        return super.getInstantiation();
    }

    /// returns the element type of the contained instantiations
    public Class<T> getType() {
        return type;
    }
}
