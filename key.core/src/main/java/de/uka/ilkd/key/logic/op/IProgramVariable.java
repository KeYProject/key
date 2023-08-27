/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TerminalProgramElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Named;

public interface IProgramVariable extends TerminalProgramElement, Named, SortedOperator {
    KeYJavaType getKeYJavaType();

    KeYJavaType getKeYJavaType(Services javaServ);

    KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec);
}
