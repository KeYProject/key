/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.abstraction;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.ty.RustType;

public record Closure() implements Type {
    @Override
    public Sort getSort(Services services) {
        return null;
    }

    @Override
    public RustType toRustType(Services services) {
        return null;
    }

    @Override
    public Name name() {
        return null;
    }
}
