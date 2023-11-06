/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.java.Expression;

import org.key_project.util.ExtList;

/**
 * represents something in logic that originates from a program like queries, program variables and
 * therefore has a KeYJavaType
 */
public interface ProgramInLogic {

    Expression convertToProgram(Term t, ExtList list);

}
