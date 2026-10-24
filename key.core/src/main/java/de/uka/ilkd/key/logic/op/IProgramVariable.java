/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.TerminalProgramElement;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;

import org.key_project.logic.op.Operator;
import org.key_project.logic.op.SortedOperator;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


@NullMarked
public interface IProgramVariable
        extends TerminalProgramElement, SortedOperator, Operator {
    @Nullable
    KeYJavaType getKeYJavaType();

    @Nullable
    KeYJavaType getKeYJavaType(Services javaServ);

    @Nullable
    KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec);
}
