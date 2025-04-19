/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.abstraction;

import de.uka.ilkd.key.java.NamedModelElement;

/**
 * An entity of the program meta model.
 *
 * @author AL
 * @author RN
 */
public interface ProgramModelElement extends NamedModelElement {

    /**
     * Returns the maximal expanded name including all applicable qualifiers.
     *
     * @return the full name of this program model element.
     */
    String getFullName();


}
