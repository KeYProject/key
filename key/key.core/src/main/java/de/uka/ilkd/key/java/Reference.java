/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.java;


/**
 * References are uses of names, variables or members. They can have a name (such as TypeReferences)
 * or be anonymous (such as ArrayReference). taken from COMPOST and changed to achieve an immutable
 * structure
 */

public interface Reference extends ProgramElement {
}
