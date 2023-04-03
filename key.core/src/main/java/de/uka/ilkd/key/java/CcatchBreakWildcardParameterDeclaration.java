package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * A "\Break *" parameter declaration of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
public class CcatchBreakWildcardParameterDeclaration extends CcatchNonstandardParameterDeclaration {

    public CcatchBreakWildcardParameterDeclaration(ExtList children) {
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        return null;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnCcatchBreakWildcardParameterDeclaration(this);
    }

}
