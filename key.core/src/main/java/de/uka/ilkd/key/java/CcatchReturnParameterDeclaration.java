package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * A "\Return" parameter declaration of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
public class CcatchReturnParameterDeclaration extends CcatchNonstandardParameterDeclaration {

    public CcatchReturnParameterDeclaration(ExtList children) {
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
        v.performActionOnCcatchReturnParameterDeclaration(this);
    }

}
