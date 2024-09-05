/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.visitor;

import java.util.ArrayDeque;
import java.util.Deque;

import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.expr.*;
import org.key_project.rusty.ast.stmt.EmptyStatement;
import org.key_project.rusty.ast.stmt.ExpressionStatement;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * Walks through a Rust AST in depth-left-fist-order.
 */
public abstract class CreatingASTVisitor extends RustyASTVisitor {
    protected static final Boolean CHANGED = Boolean.TRUE;
    protected final Deque<ExtList> stack = new ArrayDeque<>();

    boolean preservesPositionInfo = true;

    /**
     * create the CreatingASTVisitor
     *
     * @param root the ProgramElement where to begin
     * @param preservesPos whether the position should be preserved
     * @param services the services instance
     */
    public CreatingASTVisitor(RustyProgramElement root, boolean preservesPos, Services services) {
        super(root, services);
        this.preservesPositionInfo = preservesPos;
    }

    public boolean preservesPositionInfo() {
        return preservesPositionInfo;
    }

    @Override
    protected void walk(RustyProgramElement node) {
        ExtList l = new ExtList();
        // l.add(node.getPositionInfo());
        stack.push(l);
        super.walk(node);
    }

    @Override
    public String toString() {
        assert stack.peek() != null;
        return stack.peek().toString();
    }

    /**
     * called if the program element x is unchanged
     *
     * @param x The {@link RustyProgramElement}.
     */
    @Override
    protected void doDefaultAction(RustyProgramElement x) {
        addChild(x);
    }

    @Override
    public void performActionOnArithLogicalExpression(ArithLogicalExpression x) {
        throw new RuntimeException("TODO @ DD");
    }

    @Override
    public void performActionOnAssignmentExpression(AssignmentExpression x) {
        throw new RuntimeException("TODO @ DD");
    }

    @Override
    public void performActionOnBlockExpression(BlockExpression x) {
        ExtList changeList = stack.peek();
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            if (!preservesPositionInfo) {
                // TODO changeList.removeFirstOccurrence(PositionInfo.class);
            }
            var newBlock = new BlockExpression(changeList);
            addChild(newBlock);
            changed();
        } else {
            doDefaultAction(x);
        }
    }

    @Override
    public void performActionOnContextBlockExpression(ContextBlockExpression x) {
        ExtList changeList = stack.peek();
        if (!changeList.isEmpty() && changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            if (!preservesPositionInfo) {
                // TODO changeList.removeFirstOccurrence(PositionInfo.class);
            }
            var newBlock = new ContextBlockExpression(changeList);
            addChild(newBlock);
            changed();
        } else {
            doDefaultAction(x);
        }
    }

    @Override
    public void performActionOnBooleanLiteralExpression(BooleanLiteralExpression x) {
        throw new RuntimeException("TODO @ DD");
    }

    @Override
    public void performActionOnIntegerLiteralExpression(IntegerLiteralExpression x) {
        throw new RuntimeException("TODO @ DD");
    }

    @Override
    public void performActionOnNegationExpression(NegationExpression x) {
        throw new RuntimeException("TODO @ DD");
    }

    @Override
    public void performActionOnProgramVariable(ProgramVariable x) {
        throw new RuntimeException("TODO @ DD");
    }

    @Override
    public void performActionOnSchemaVariable(SchemaVariable x) {
        throw new RuntimeException("TODO @ DD");
    }

    @Override
    public void performActionOnEmptyStatement(EmptyStatement x) {
        doDefaultAction(x);
    }

    @Override
    public void performActionOnExpressionStatement(ExpressionStatement x) {
        ExtList changeList = stack.peek();
        if (!changeList.isEmpty() && changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            Expr expr = changeList.removeFirstOccurrence(Expr.class);
            addChild(new ExpressionStatement(expr));
            changed();
        } else {
            doDefaultAction(x);
        }
    }

    protected void changed() {
        ExtList list = stack.peek();
        if (list.isEmpty() || list.getFirst() != CHANGED) {
            list.addFirst(CHANGED);
        }
    }

    protected void addToTopOfStack(RustyProgramElement x) {
        if (x != null) {
            ExtList list = stack.peek();
            list.add(x);
        }
    }

    protected void addChild(RustyProgramElement x) {
        stack.pop();
        addToTopOfStack(x);
    }

    protected void addChildren(ImmutableArray<RustyProgramElement> arr) {
        stack.pop();
        for (int i = 0, sz = arr.size(); i < sz; i++) {
            addToTopOfStack(arr.get(i));
        }
    }

    protected abstract class DefaultAction {
        protected final RustyProgramElement pe;

        protected DefaultAction(RustyProgramElement pe) {
            this.pe = pe;
        }

        abstract RustyProgramElement createNewElement(ExtList changeList);

        public void doAction(RustyProgramElement x) {
            ExtList changeList = stack.peek();
            assert changeList != null;
            if (changeList.isEmpty()) {
                doDefaultAction(x);
                return;
            }
            if (changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
                /*
                 * if (!preservesPositionInfo) {
                 * changeList.removeFirstOccurrence(PositionInfo.class);
                 * }
                 */
                addNewChild(changeList);
            } else {
                doDefaultAction(x);
            }
        }

        protected void addNewChild(ExtList changeList) {
            addChild(createNewElement(changeList));
            changed();
        }
    }
}
