/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.statement;

import de.uka.ilkd.key.java.ast.LoopInitializer;
import de.uka.ilkd.key.java.ast.NonTerminalProgramElement;

import org.key_project.util.collection.ImmutableArray;

public interface ILoopInit extends NonTerminalProgramElement {

    int size();

    ImmutableArray<LoopInitializer> getInits();

}
