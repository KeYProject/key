/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.ast.expression.Expression;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NullMarked;

/**
 * represents something in logic that originates from a program like queries, program variables and
 * therefore has a KeYJavaType
 */
@NullMarked
public interface ProgramInLogic {

    Expression convertToProgram(JTerm t, ExtList list);

}
