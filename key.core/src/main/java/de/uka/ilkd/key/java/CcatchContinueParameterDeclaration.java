package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

import java.util.List;

/**
 * A "\Continue" parameter declaration of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
public class CcatchContinueParameterDeclaration extends CcatchNonstandardParameterDeclaration {

    public CcatchContinueParameterDeclaration(ExtList children) {
        super();
    }

    public CcatchContinueParameterDeclaration(PositionInfo pi, List<Comment> c) {
        super(pi, c);
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
        v.performActionOnCcatchContinueParameterDeclaration(this);
    }

}
