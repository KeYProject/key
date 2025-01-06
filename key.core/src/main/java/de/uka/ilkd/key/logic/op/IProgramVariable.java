/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TerminalProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;


public interface IProgramVariable
        extends TerminalProgramElement, org.key_project.logic.op.SortedOperator, Operator {
    KeYJavaType getKeYJavaType();

    KeYJavaType getKeYJavaType(Services javaServ);

    KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec);
}
