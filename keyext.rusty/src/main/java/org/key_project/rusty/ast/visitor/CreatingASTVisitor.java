/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.visitor;

import java.util.ArrayDeque;
import java.util.Deque;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.Label;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.expr.*;
import org.key_project.rusty.ast.stmt.EmptyStatement;
import org.key_project.rusty.ast.stmt.ExpressionStatement;
import org.key_project.rusty.ast.stmt.LetStatement;
import org.key_project.rusty.logic.op.ProgramVariable;
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
    protected CreatingASTVisitor(RustyProgramElement root, boolean preservesPos,
            Services services) {
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
    public void performActionOnAssignmentExpression(AssignmentExpression x) {
        var def = new DefaultAction(x) {
            @Override
            RustyProgramElement createNewElement(ExtList changeList) {
                return new AssignmentExpression(changeList);
            }
        };
        def.doAction(x);
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
        doDefaultAction(x);
    }

    @Override
    public void performActionOnIntegerLiteralExpression(IntegerLiteralExpression x) {
        doDefaultAction(x);
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
            addChild(new ExpressionStatement(expr, x.hasSemi()));
            changed();
        } else {
            doDefaultAction(x);
        }
    }

    @Override
    public void performActionOnLetStatement(LetStatement x) {
        DefaultAction def = new DefaultAction(x) {
            @Override
            RustyProgramElement createNewElement(ExtList changeList) {
                return new LetStatement(changeList);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnUnaryExpression(UnaryExpression x) {
        DefaultAction def = new DefaultAction(x) {
            @Override
            RustyProgramElement createNewElement(ExtList changeList) {
                return new UnaryExpression(changeList);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnLetExpression(LetExpression x) {
        DefaultAction def = new DefaultAction(x) {
            @Override
            RustyProgramElement createNewElement(ExtList changeList) {
                return new LetExpression(changeList);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnIfExpression(IfExpression x) {
        DefaultAction def = new DefaultAction(x) {
            @Override
            RustyProgramElement createNewElement(ExtList changeList) {
                return new IfExpression(changeList);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnBinaryExpression(BinaryExpression x) {
        DefaultAction def = new DefaultAction(x) {
            @Override
            RustyProgramElement createNewElement(ExtList changeList) {
                return new BinaryExpression(changeList);
            }
        };
        def.doAction(x);
    }

    protected void performActionOnLoopInvariant(InfiniteLoopExpression old,
            InfiniteLoopExpression newLoop) {

    }

    @Override
    public void performActionOnInfiniteLoop(InfiniteLoopExpression x) {
        ExtList changeList = stack.peek();
        if (!changeList.isEmpty() && changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            Label l = changeList.removeFirstOccurrence(Label.class);
            Expr body = changeList.removeFirstOccurrence(Expr.class);

            var nl = new InfiniteLoopExpression(l, body);
            performActionOnLoopInvariant(x, nl);
            addChild(nl);

            changed();
        } else {
            doDefaultAction(x);
            performActionOnLoopInvariant(x, x);
        }
    }

    @Override
    public void performActionOnBreakExpression(BreakExpression x) {
        DefaultAction def = new DefaultAction(x) {
            @Override
            RustyProgramElement createNewElement(ExtList changeList) {
                var label = changeList.get(Label.class);
                var expr = changeList.get(Expr.class);
                return new BreakExpression(label, expr);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnCompoundAssignmentExpression(CompoundAssignmentExpression x) {
        DefaultAction def = new DefaultAction(x) {
            @Override
            RustyProgramElement createNewElement(ExtList changeList) {
                return new CompoundAssignmentExpression(changeList);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnLoopScope(LoopScope x) {
        DefaultAction def = new DefaultAction(x) {
            @Override
            RustyProgramElement createNewElement(ExtList changeList) {
                return new LoopScope(changeList);
            }
        };
        def.doAction(x);
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
