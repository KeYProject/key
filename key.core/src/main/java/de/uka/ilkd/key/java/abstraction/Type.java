/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.abstraction;

import de.uka.ilkd.key.java.expression.Literal;

/**
 * A program model element representing types.
 *
 * @author AL
 * @author RN
 */
public interface Type extends ProgramModelElement {

    /**
     * returns the default value of the given type according to JLS Sect. 4.5.5
     *
     * @return the default value of the given type according to JLS Sect. 4.5.5
     */
    Literal getDefaultValue();

}
