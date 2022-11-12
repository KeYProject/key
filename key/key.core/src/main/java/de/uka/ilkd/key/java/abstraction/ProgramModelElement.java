/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.java.abstraction;

/**
 * An entity of the program meta model.
 *
 * @author AL
 * @author RN
 */
public interface ProgramModelElement extends de.uka.ilkd.key.java.NamedModelElement {

    /**
     * Returns the maximal expanded name including all applicable qualifiers.
     *
     * @return the full name of this program model element.
     */
    String getFullName();


}
