package org.key_project.rusty.ast.visitor;

import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.expr.*;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.logic.op.sv.ProgramSV;
import org.key_project.rusty.logic.op.sv.SchemaVariable;

/**
 * Extends the RustyASTWalker to use the visitor mechanism. The methods inherited by the Visitor
 * interface are all implemented that they call the method
 * <code> doDefaultAction(ProgramElement) </code>.
 */
public abstract class RustyASTVisitor extends RustyASTWalker implements Visitor {
    protected final Services services;

    /**
     * create the JavaASTVisitor
     *
     * @param root the ProgramElement where to begin
     * @param services the Services object
     */
    public RustyASTVisitor(RustyProgramElement root, Services services) {
        super(root);
        this.services = services;
    }

    /**
     * the action that is performed just before leaving the node the last time
     */
    @Override
    protected void doAction(RustyProgramElement node) {
        node.visit(this);
    }

    /**
     * the action that is performed just before leaving the node the last time
     *
     * @param node the node described above
     */
    protected abstract void doDefaultAction(RustyProgramElement node);

    @Override
    public void performActionOnArithLogicalExpression(ArithLogicalExpression x) {
doDefaultAction(x);
    }

    @Override
    public void performActionOnAssignmentExpression(AssignmentExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnBlockExpression(BlockExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnBooleanLiteralExpression(BooleanLiteralExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnContextBlockExpression(ContextBlockExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnIntegerLiteralExpression(IntegerLiteralExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnNegationExpression(NegationExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnProgramVariable(ProgramVariable x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnSchemaVariable(SchemaVariable x) {
        doDefaultAction((ProgramSV) x);
    }
}
