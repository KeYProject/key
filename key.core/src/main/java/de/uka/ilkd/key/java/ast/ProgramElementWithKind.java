/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast;

/**
 * Common interface for BinaryAssignment, UnaryOperator, BinaryOperator, LogicFunctinalOperator and
 * Modifier
 *
 * @param <K> specifies the concrete kind of the program element, e.g. whether it is a logical-and
 *        or a logical-or
 */
public interface ProgramElementWithKind<K extends Enum<K>> extends ProgramElement {
    K getKind();
}
