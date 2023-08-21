/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.PosInProgram;

/**
 * this class is created if the scheme given by a context term has matched to a java program. The
 * ContextStatementBlockInstantiation class stores the instantiations of the prefix and the suffix.
 */
public class ContextStatementBlockInstantiation {

    /** the end position of the prefix omega */
    private final PosInProgram prefixEnd;

    /** the start position of the suffix omega */
    private final PosInProgram suffixStart;

    /** the execution context of the first active statement */
    private final ExecutionContext activeStatementContext;

    /** the whole program element this context term inst refers to */
    private final ProgramElement programElement;

    /**
     * creates a ContextStatementBlockInstantiation of a context term
     *
     * @param prefixEnd the PosInProgram describing the first statement after the end of the prefix
     * @param suffixStart the PosInProgram describing the statement just before the suffix begins
     * @param activeStatementContext the ExecutionContext of the first active statement
     * @param pe the ProgramElement the context positions are related to
     */
    public ContextStatementBlockInstantiation(PosInProgram prefixEnd, PosInProgram suffixStart,
            ExecutionContext activeStatementContext, ProgramElement pe) {

        this.prefixEnd = prefixEnd;
        this.suffixStart = suffixStart;
        this.activeStatementContext = activeStatementContext;
        this.programElement = pe;
    }

    /**
     * returns the end position of the prefix
     *
     * @return the end position of the prefix
     */
    public PosInProgram prefix() {
        return prefixEnd;
    }

    /**
     * returns the PosInProgram describing the statement just before the suffix begins
     */
    public PosInProgram suffix() {
        return suffixStart;
    }

    /**
     * returns the execution context of the first active statement or null if match is performed
     * outer most
     */
    public ExecutionContext activeStatementContext() {
        return activeStatementContext;
    }

    /**
     * returns the program element this context term instantiation refers to
     *
     * @return returns the program element this context term instantiation refers to
     */
    public ProgramElement programElement() {
        return programElement;
    }

    public boolean equals(Object o) {
        if (!(o instanceof ContextStatementBlockInstantiation)) {
            return false;
        }
        final ContextStatementBlockInstantiation inst = (ContextStatementBlockInstantiation) o;

        if (isDifferent(suffixStart, inst.suffixStart)) {
            return false;
        }

        if (isDifferent(prefixEnd, inst.prefixEnd)) {
            return false;
        }

        if (isDifferent(activeStatementContext, inst.activeStatementContext)) {
            return false;
        }

        return !isDifferent(programElement, inst.programElement);

    }

    private boolean isDifferent(Object self, Object other) {
        if (self != null && other != null) {
            return !self.equals(other);
        } else {
            return self != other;
        }
    }

    public int hashCode() {
        int hashCode = 1;
        if (prefixEnd != null) {
            hashCode = 17 * prefixEnd.hashCode();
        }
        if (suffixStart != null) {
            hashCode += 17 * suffixStart.hashCode();
        }
        if (activeStatementContext != null) {
            hashCode += 17 * activeStatementContext.hashCode();
        }
        if (programElement != null) {
            hashCode += 17 * programElement.hashCode();
        }
        return hashCode;
    }

    /** toString */
    public String toString() {
        String result = "ContextStatementBlockInstantiation:\n";
        result += "Prefix ends before " + prefixEnd.toString();
        result += "\nSuffix starts after " + suffixStart.toString();
        result += "\nFirst active statement has execution context  " + activeStatementContext;
        result += "\nRefers to Program " + programElement;
        return result + "\n";
    }
}
