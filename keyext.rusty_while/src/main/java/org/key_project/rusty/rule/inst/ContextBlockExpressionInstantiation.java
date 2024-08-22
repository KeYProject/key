package org.key_project.rusty.rule.inst;

import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.logic.PosInProgram;

/**
 * this class is created if the scheme given by a context term has matched to a Rust program. The
 * ContextBlockExpressionInstantiation class stores the instantiations of the prefix and the suffix.
 */
public class ContextBlockExpressionInstantiation {
    /** the end position of the prefix omega */
    private final PosInProgram prefixEnd;

    /** the start position of the suffix omega */
    private final PosInProgram suffixStart;

    /** the whole program element this context term inst refers to */
    private final RustyProgramElement programElement;

    /**
     * creates a ContextStatementBlockInstantiation of a context term
     *
     * @param prefixEnd the PosInProgram describing the first statement after the end of the prefix
     * @param suffixStart the PosInProgram describing the statement just before the suffix begins
     * @param pe the ProgramElement the context positions are related to
     */
    public ContextBlockExpressionInstantiation(PosInProgram prefixEnd, PosInProgram suffixStart,
                                              RustyProgramElement pe) {

        this.prefixEnd = prefixEnd;
        this.suffixStart = suffixStart;
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
     * returns the program element this context term instantiation refers to
     *
     * @return returns the program element this context term instantiation refers to
     */
    public RustyProgramElement programElement() {
        return programElement;
    }

    public boolean equals(Object o) {
        if (!(o instanceof ContextBlockExpressionInstantiation inst)) {
            return false;
        }

        if (isDifferent(suffixStart, inst.suffixStart)) {
            return false;
        }

        if (isDifferent(prefixEnd, inst.prefixEnd)) {
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
        result += "\nRefers to Program " + programElement;
        return result + "\n";
    }
}
