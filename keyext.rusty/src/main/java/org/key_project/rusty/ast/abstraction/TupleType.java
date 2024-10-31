/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.abstraction;

import java.util.List;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;

public class TupleType implements Type {
    public static final TupleType UNIT = new TupleType();

    public static TupleType getInstance(List<Type> types) {

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
