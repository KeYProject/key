/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.varcond;

import org.key_project.logic.ParsableVariable;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.ast.abstraction.KeYRustyType;

/**
 * Argument types for {@link TacletBuilderCommand}s.
 *
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 * @see TacletBuilderCommand
 */
public enum ArgumentType {
    /* TYPE_RESOLVER(TypeResolver.class), */ SORT(Sort.class), TERM(Term.class),
    RUST_TYPE(KeYRustyType.class), VARIABLE(ParsableVariable.class), STRING(String.class);

    public final Class<?> clazz;

    ArgumentType(Class<?> clazz) {
        this.clazz = clazz;
    }
}
