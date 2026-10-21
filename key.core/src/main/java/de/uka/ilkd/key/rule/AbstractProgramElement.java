/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;

public interface AbstractProgramElement extends ProgramElement {

    ProgramElement getConcreteProgramElement(Services services);

}
