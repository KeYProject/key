package de.uka.ilkd.key.java;

import java.util.List;

import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * A "\Break label" parameter declaration of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
public class CcatchBreakLabelParameterDeclaration extends CcatchNonstandardParameterDeclaration {

    private final Label label;

    public CcatchBreakLabelParameterDeclaration(ExtList children) {
        label = children.get(Label.class);
    }

    public CcatchBreakLabelParameterDeclaration(PositionInfo pi, List<Comment> c, Label label) {
        super(pi, c);
        this.label = label;
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
            if (index == 0) {
                return label;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnCcatchBreakLabelParameterDeclaration(this);
    }

}
