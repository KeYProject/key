/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.abstraction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;

public class TupleType implements Type {
    public static final TupleType UNIT = getInstance(new ArrayList<>());
    private static Map<List<Type>, TupleType> TYPES = null;

    private List<Type> types;

    public TupleType(List<Type> types) {
        this.types = types;
    }

    public static TupleType getInstance(List<Type> types) {
        if (TYPES == null) {
            TYPES = new HashMap<>();
        }
        return TYPES.computeIfAbsent(types, t -> new TupleType(types));
    }

    public List<Type> getTypes() {
        return types;
    }

    @Override
    public Sort getSort(Services services) {
        return null;
    }

    @Override
    public Name name() {
        return null;
    }
}
