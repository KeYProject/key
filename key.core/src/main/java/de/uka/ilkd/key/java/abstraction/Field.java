/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.abstraction;

import de.uka.ilkd.key.logic.op.IProgramVariable;

/**
 * A program model element representing fields.
 *
 * @author AL
 * @author RN The file has been modified by the KeY team.
 */
public interface Field extends Variable, Member {

    /**
     * returns the program variable associated with this field
     *
     * @return the program variable associated with this field
     */
    IProgramVariable getProgramVariable();

    /**
     * returns the name of the field as used in programs. In the logic each field has a unique name
     * which is composed by the class name where it is declared and its source code name
     *
     * @return returns the name of the field as used in programs
     */
    String getProgramName();

}
