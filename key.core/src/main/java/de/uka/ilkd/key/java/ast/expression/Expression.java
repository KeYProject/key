/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.expression;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Expression taken from COMPOST and changed to achieve an immutable structure
 */
@NullMarked
public interface Expression extends ProgramElement {
    /**
     * returns the {@link KeYJavaType} of an expression
     *
     * @param ec the execution context in which the expression is evaluated, if any; expressions
     *        that do not depend on a context (e.g. variables with declared types) resolve their
     *        own type when no context is available and {@code ec} may be {@code null}
     */
    @Nullable
    KeYJavaType getKeYJavaType(Services javaServ, @Nullable ExecutionContext ec);
}
