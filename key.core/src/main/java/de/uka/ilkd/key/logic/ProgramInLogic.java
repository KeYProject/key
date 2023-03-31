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
