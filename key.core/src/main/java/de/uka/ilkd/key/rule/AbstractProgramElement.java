/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;

public interface AbstractProgramElement extends ProgramElement {

    ProgramElement getConcreteProgramElement(Services services);

}
