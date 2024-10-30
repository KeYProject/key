/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.logic.op.LocationVariable;

import org.key_project.util.collection.ImmutableMap;

import org.jspecify.annotations.NonNull;

public class LocationVarMap
        extends InstantiationEntry<ImmutableMap<@NonNull LocationVariable, LocationVariable>> {
    /**
     * creates a new instantiation entry for the instantiation to be stored
     *
     * @param instantiation the instantiation to be stored
     */
    public LocationVarMap(ImmutableMap<@NonNull LocationVariable, LocationVariable> instantiation) {
        super(instantiation);
    }
}
