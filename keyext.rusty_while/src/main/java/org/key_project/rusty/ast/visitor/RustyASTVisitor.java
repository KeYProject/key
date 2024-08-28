/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.visitor;

import org.key_project.rusty.Services;
import org.key_project.rusty.ast.PathInExpression;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.expr.*;
import org.key_project.rusty.ast.fn.SelfParam;
import org.key_project.rusty.ast.stmt.EmptyStatement;
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
     * create the RustyASTVisitor
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

    @Override
    public void performActionOnEmptyStatement(EmptyStatement x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnBorrowExpression(BorrowExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnBreakExpression(BreakExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnCallExpression(CallExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnClosureExpression(ClosureExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnComparisonExpression(ComparisonExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnCompoundAssignmentExpression(CompoundAssignmentExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnContinueExpression(ContinueExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnDereferenceExpression(DereferenceExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnEnumeratedArrayExpression(EnumeratedArrayExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnEnumVariantFieldless(EnumVariantFieldless x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnEnumVariantTuple(EnumVariantTuple x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnErrorPropagationExpression(ErrorPropagationExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnFieldExpression(FieldExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnFieldStructExpression(StructStructExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnGroupedExpression(GroupedExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnIndexExpression(IndexExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnLazyBooleanExpression(LazyBooleanExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnMethodCall(MethodCallExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnPathInExpression(PathInExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnRangeExpression(RangeExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnRepeatedArrayExpression(RepeatedArrayExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnReturnExpression(ReturnExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnSelfParam(SelfParam x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnTupleExpression(TupleExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnTupleIndexingExpression(TupleIndexingExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnTupleStructExpression(TupleStructExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnTypeCastExpression(TypeCastExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnUnitStructExpression(UnitStructExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnEnumVariantStruct(EnumVariantStruct x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnIfExpression(IfExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnIfLetExpression(IfLetExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnInfiniteLoop(InfiniteLoopExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnIteratorLoopExpression(IteratorLoopExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnMatchArm(MatchArm x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnMatchExpression(MatchExpression x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnPredicatePatternLoopExpression(PredicatePatternLoopExpression x) {
        doDefaultAction(x);
    }
}
