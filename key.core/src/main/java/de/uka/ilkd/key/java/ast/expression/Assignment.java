/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression;

import de.uka.ilkd.key.java.ast.ExpressionContainer;
import de.uka.ilkd.key.java.ast.NonTerminalProgramElement;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.ProgramElementWithKind;
import de.uka.ilkd.key.java.ast.SourceElement;

/**
 * Role interface to catch assignments via one type check.
 * An assignment is an operator with side-effects.
 */
public interface Assignment<K extends Enum<K> & AssignmentKind>
        extends SourceElement, ProgramElement, NonTerminalProgramElement, Expression,
        ExpressionContainer, ExpressionStatement, ProgramElementWithKind<K> {

    @Override
    K getKind();
}
