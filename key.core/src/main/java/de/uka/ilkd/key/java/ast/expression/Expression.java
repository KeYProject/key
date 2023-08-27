/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;


/**
 * Expression taken from COMPOST and changed to achieve an immutable structure
 */
public interface Expression extends ProgramElement {
    /**
     * returns the {@link KeYJavaType} of an expression
     */
    KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec);
}
