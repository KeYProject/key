package de.uka.ilkd.key.java;

import java.io.IOException;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.visitor.Visitor;

/**
 * A "\Continue label" parameter declaration of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
public class CcatchContinueLabelParameterDeclaration extends CcatchNonstandardParameterDeclaration {

    private final Label label;

    public CcatchContinueLabelParameterDeclaration(ExtList children) {
        label = children.get(Label.class);
    }

    @Override
    public int getChildCount() {
        return (label != null) ? 1 : 0;
    }

    public Label getLabel() {
        return label;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        if (label != null) {
            if (index == 0)
                return label;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnCCcatchContinueLabelParameterDeclaration(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter w) throws IOException {
        w.printCcatchContinueLabelParameterDeclaration(this);
    }

}
