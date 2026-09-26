/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast;


/**
 * References are uses of names, variables or members. They can have a name (such as TypeReferences)
 * or be anonymous (such as ArrayReference). taken from COMPOST and changed to achieve an immutable
 * structure
 */

public interface Reference extends ProgramElement {
}
