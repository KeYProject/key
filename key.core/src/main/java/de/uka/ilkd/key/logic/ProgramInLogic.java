package de.uka.ilkd.key.logic;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;

/**
 * represents something in logic that originates from a program like queries, program variables and
 * therefore has a KeYJavaType
 */
public interface ProgramInLogic {

    Expression convertToProgram(Term t, ExtList list);

}
