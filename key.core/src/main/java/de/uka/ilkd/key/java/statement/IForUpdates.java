/*
 * This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0
 */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.Expression;

import org.key_project.util.collection.ImmutableArray;

public interface IForUpdates extends de.uka.ilkd.key.java.TerminalProgramElement {

    int size();

    Expression getExpressionAt(int i);

    ImmutableArray<Expression> getUpdates();

}
