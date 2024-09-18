/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.ty;

import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.abstraction.Type;

/**
 * A type occurring in Rust code.
 */
public interface RustType extends RustyProgramElement {
    Type type();

    default Sort getSort(Services services) {
        return type().getSort(services);
    }
}
