package de.uka.ilkd.key.java;

import java.util.List;

/**
 * A "non-standard" parameter declaration of a Ccatch clause, e.g., "\Return".
 *
 * @author Dominic Steinhöfel
 */
public abstract class CcatchNonstandardParameterDeclaration extends JavaNonTerminalProgramElement {

    public CcatchNonstandardParameterDeclaration(PositionInfo pi, List<Comment> c) {
        super(pi, c);
    }

    public CcatchNonstandardParameterDeclaration() {

    }
}
