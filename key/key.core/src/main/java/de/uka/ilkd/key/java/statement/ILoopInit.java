/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.java.statement;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.LoopInitializer;
import de.uka.ilkd.key.java.TerminalProgramElement;

public interface ILoopInit extends TerminalProgramElement {

    int size();

    ImmutableArray<LoopInitializer> getInits();

}
