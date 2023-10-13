/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.varexp;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.conditions.TypeResolver;

/**
 * Argument types for {@link TacletBuilderCommand}s.
 *
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 * @see TacletBuilderCommand
 */
public enum ArgumentType {
    TYPE_RESOLVER(TypeResolver.class), SORT(Sort.class), TERM(Term.class),
    JAVA_TYPE(KeYJavaType.class), VARIABLE(ParsableVariable.class), STRING(String.class);

    public final Class<?> clazz;

    ArgumentType(Class<?> clazz) {
        this.clazz = clazz;
    }
}
