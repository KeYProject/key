/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.NonTerminalProgramElement;

import org.key_project.util.collection.ImmutableArray;

public interface IForUpdates extends NonTerminalProgramElement {

    int size();

    Expression getExpressionAt(int i);

    ImmutableArray<Expression> getUpdates();

}
