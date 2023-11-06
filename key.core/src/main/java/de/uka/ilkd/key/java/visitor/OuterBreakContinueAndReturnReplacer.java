/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.util.ExtList;

public class OuterBreakContinueAndReturnReplacer extends JavaASTVisitor {

    protected static final Boolean CHANGED = Boolean.TRUE;

    private final Break breakOut;
    private final Map<Label, ProgramVariable> breakFlags;
    private final Map<Label, ProgramVariable> continueFlags;
    private final ProgramVariable returnFlag;
    private final ProgramVariable returnValue;
    private final ProgramVariable exception;

    private final ArrayDeque<ExtList> stack = new ArrayDeque<>();
    private final ArrayDeque<Label> labels = new ArrayDeque<>();
    private final ArrayDeque<MethodFrame> frames = new ArrayDeque<>();
    private int loopAndSwitchCascadeDepth;

    private StatementBlock result;

    public OuterBreakContinueAndReturnReplacer(final StatementBlock block,
            final Iterable<Label> alwaysInnerLabels, final Label breakOutLabel,
            final Map<Label, ProgramVariable> breakFlags,
            final Map<Label, ProgramVariable> continueFlags, final ProgramVariable returnFlag,
            final ProgramVariable returnValue, final ProgramVariable exception,
            final Services services) {
        super(block, services);
        for (Label label : alwaysInnerLabels) {
            this.labels.push(label);
        }
        this.breakOut = new Break(breakOutLabel);
        this.breakFlags = breakFlags;
        this.continueFlags = continueFlags;
        this.returnFlag = returnFlag;
        this.returnValue = returnValue;
        this.exception = exception;
    }

    public StatementBlock replace() {
        start();
        return result;
    }

    @Override
    public void start() {
        loopAndSwitchCascadeDepth = 0;
        stack.push(new ExtList());
        super.start();
        ExtList el = stack.peek();
        int i = (el.get(0) == CHANGED ? 1 : 0);
        result = (StatementBlock) el.get(i);
    }

    public StatementBlock getResult() {
        return result;
    }

    @Override
    protected void walk(final ProgramElement node) {
        if (node.getPositionInfo() != PositionInfo.UNDEFINED) {
            stack.push(new ExtList(new Object[] { node.getPositionInfo() }));
        } else {
            stack.push(new ExtList());
        }
        if (node instanceof LoopStatement || node instanceof Switch) {
            loopAndSwitchCascadeDepth++;
        }
        if (node instanceof LabeledStatement) {
            labels.push(((LabeledStatement) node).getLabel());
        }
        if (node instanceof MethodFrame) {
            frames.push((MethodFrame) node);
        }
        super.walk(node);
        if (node instanceof MethodFrame) {
            frames.pop();
        }
        if (node instanceof LabeledStatement) {
            labels.pop();
        }
        if (node instanceof LoopStatement || node instanceof Switch) {
            loopAndSwitchCascadeDepth--;
        }
    }

    @Override
    public String toString() {
        return stack.peek().toString();
    }

    @Override
    protected void doDefaultAction(final SourceElement x) {
        addChild(x);
    }

    @Override
    public void performActionOnBreak(final Break x) {
        performActionOnJump(x, breakFlags);
    }

    @Override
    public void performActionOnContinue(final Continue x) {
        performActionOnJump(x, continueFlags);
    }

    private void performActionOnJump(final LabelJumpStatement x,
            final Map<Label, ProgramVariable> flags) {
        if (isJumpToOuterLabel(x)) {
            final ProgramVariable flag = flags.get(x.getLabel());
            assert flag != null : "a label flag must not be null";
            final Statement assign =
                KeYJavaASTFactory.assign(flag, BooleanLiteral.TRUE, x.getPositionInfo());
            final Statement[] statements = new Statement[] { assign, breakOut };
            addChild(new StatementBlock(statements));
            changed();
        } else {
            doDefaultAction(x);
        }
    }

    private boolean isJumpToOuterLabel(final LabelJumpStatement x) {
        return loopAndSwitchCascadeDepth == 0 && x.getProgramElementName() == null
                || x.getLabel() != null && !labels.contains(x.getLabel());
    }

    @Override
    public void performActionOnReturn(final Return x) {
        if (frames.isEmpty()) {
            final ExtList changeList = stack.peek();
            if (!changeList.isEmpty() && changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
            }
            Statement assignFlag =
                KeYJavaASTFactory.assign(returnFlag, BooleanLiteral.TRUE, x.getPositionInfo());
            final Statement[] statements;
            if (returnValue == null) {
                statements = new Statement[] { assignFlag, breakOut };
            } else {
                Statement assignValue =
                    KeYJavaASTFactory.assign(returnValue, x.getExpression(), x.getPositionInfo());
                statements = new Statement[] { assignFlag, assignValue, breakOut };
            }
            addChild(new StatementBlock(statements));
            changed();
        } else {
            doDefaultAction(x);
        }
    }

    @Override
    public void performActionOnLocalVariableDeclaration(final LocalVariableDeclaration x) {
        DefaultAction def = new DefaultAction() {
            @Override
            ProgramElement createNewElement(final ExtList changeList) {
                return new LocalVariableDeclaration(changeList);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnStatementBlock(final StatementBlock x) {
        DefaultAction def = new DefaultAction() {
            @Override
            ProgramElement createNewElement(final ExtList changeList) {
                return new StatementBlock(changeList);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnWhile(final While x) {
        final ExtList changeList = stack.peek();
        if (!changeList.isEmpty() && changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            Expression guard = ((Guard) changeList.removeFirst()).getExpression();
            Statement body = (Statement) (changeList.isEmpty() ? null : changeList.removeFirst());
            While newLoop = new While(guard, body, x.getPositionInfo());
            services.getSpecificationRepository().copyLoopInvariant(x, newLoop);
            addChild(newLoop);
            changed();
        } else {
            doDefaultAction(x);
        }
    }

    @Override
    public void performActionOnFor(final For x) {
        DefaultAction def = new DefaultAction() {
            @Override
            ProgramElement createNewElement(final ExtList changeList) {
                For newLoop = new For(changeList);
                services.getSpecificationRepository().copyLoopInvariant(x, newLoop);
                return newLoop;
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnEnhancedFor(final EnhancedFor x) {
        DefaultAction def = new DefaultAction() {
            @Override
            ProgramElement createNewElement(final ExtList changeList) {
                EnhancedFor newLoop = new EnhancedFor(changeList);
                services.getSpecificationRepository().copyLoopInvariant(x, newLoop);
                return newLoop;
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnDo(final Do x) {
        final ExtList changeList = stack.peek();
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            Statement body = changeList.removeFirstOccurrence(Statement.class);
            Guard g = changeList.removeFirstOccurrence(Guard.class);
            Expression guard = g == null ? null : g.getExpression();
            Do newLoop = new Do(guard, body, x.getPositionInfo());
            services.getSpecificationRepository().copyLoopInvariant(x, newLoop);
            addChild(newLoop);
            changed();
        } else {
            doDefaultAction(x);
        }
    }

    @Override
    public void performActionOnIf(final If x) {
        DefaultAction def = new DefaultAction() {
            @Override
            ProgramElement createNewElement(final ExtList changeList) {
                return new If(changeList);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnSwitch(final Switch x) {
        DefaultAction def = new DefaultAction() {
            @Override
            ProgramElement createNewElement(final ExtList changeList) {
                return new Switch(changeList);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnTry(final Try x) {
        DefaultAction def = new DefaultAction() {
            @Override
            ProgramElement createNewElement(final ExtList changeList) {
                return new Try(changeList);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnLabeledStatement(final LabeledStatement x) {
        Label l = null;
        final ExtList changeList = stack.peek();
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            if (x.getLabel() != null) {
                l = (Label) changeList.removeFirst();
            }
            addChild(new LabeledStatement(changeList, l, x.getPositionInfo()));
            changed();
        } else {
            doDefaultAction(x);
        }
    }

    @Override
    public void performActionOnMethodFrame(final MethodFrame x) {
        final ExtList changeList = stack.peek();
        if (!changeList.isEmpty() && changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            if (x.getChildCount() == 3) {
                addChild(new MethodFrame((IProgramVariable) changeList.get(0),
                    (IExecutionContext) changeList.get(1), (StatementBlock) changeList.get(2),
                    PositionInfo.UNDEFINED));

            } else if (x.getChildCount() == 2) {
                addChild(new MethodFrame(null, (IExecutionContext) changeList.get(0),
                    (StatementBlock) changeList.get(1), PositionInfo.UNDEFINED));
            } else {
                throw new IllegalStateException("Method-frame has wrong number of children.");
            }
            changed();
        } else {
            doDefaultAction(x);
        }
    }

    @Override
    public void performActionOnSynchronizedBlock(final SynchronizedBlock x) {
        DefaultAction def = new DefaultAction() {
            @Override
            ProgramElement createNewElement(final ExtList changeList) {
                return new SynchronizedBlock(changeList);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnCopyAssignment(final CopyAssignment x) {
        DefaultAction def = new DefaultAction() {
            @Override
            ProgramElement createNewElement(final ExtList changeList) {
                return new CopyAssignment(changeList);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnThen(final Then x) {
        DefaultAction def = new DefaultAction() {
            @Override
            ProgramElement createNewElement(final ExtList changeList) {
                return new Then(changeList);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnElse(final Else x) {
        DefaultAction def = new DefaultAction() {
            @Override
            ProgramElement createNewElement(final ExtList changeList) {
                return new Else(changeList);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnCase(final Case x) {
        Expression e = null;
        final ExtList changeList = stack.peek();
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            if (x.getExpression() != null) {
                e = (Expression) changeList.removeFirst();
            }
            addChild(new Case(changeList, e, x.getPositionInfo()));
            changed();
        } else {
            doDefaultAction(x);
        }
    }

    @Override
    public void performActionOnCatch(final Catch x) {
        DefaultAction def = new DefaultAction() {
            @Override
            ProgramElement createNewElement(final ExtList changeList) {
                return new Catch(changeList);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnCcatch(final Ccatch x) {
        DefaultAction def = new DefaultAction() {
            @Override
            ProgramElement createNewElement(final ExtList changeList) {
                return new Ccatch(changeList);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnDefault(final Default x) {
        DefaultAction def = new DefaultAction() {
            @Override
            ProgramElement createNewElement(final ExtList changeList) {
                return new Default(changeList);
            }
        };
        def.doAction(x);
    }

    @Override
    public void performActionOnFinally(final Finally x) {
        final ExtList statements;
        final ExtList changeList = stack.peek();
        if (changeList.size() > 0 && changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            statements = changeList;
        } else {
            statements = new ExtList();
            statements.add(x.getBody());
        }

        Map<ProgramVariable, ProgramVariable> oldFlags = new HashMap<>();

        {
            for (ProgramVariable flag : breakFlags.values()) {
                addOldFlag(oldFlags, flag);
            }

            for (ProgramVariable flag : continueFlags.values()) {
                addOldFlag(oldFlags, flag);
            }

            addOldFlag(oldFlags, returnFlag);
            addOldFlag(oldFlags, exception);
        }

        ExtList newStatements = new ExtList();

        {
            // Remember current flags.
            for (Entry<ProgramVariable, ProgramVariable> entry : oldFlags.entrySet()) {
                newStatements.add(KeYJavaASTFactory.declare(entry.getValue(), entry.getKey(),
                    entry.getValue().getKeYJavaType()));
            }

            // Reset flags.
            for (ProgramVariable flag : oldFlags.keySet()) {
                newStatements.add(
                    KeYJavaASTFactory.assign(flag, flag.getKeYJavaType().getDefaultValue()));
            }

            // Execute finally-block.
            newStatements.addAll(statements);

            // Restore flags.
            for (Entry<ProgramVariable, ProgramVariable> entry : oldFlags.entrySet()) {
                newStatements.add(KeYJavaASTFactory.assign(entry.getKey(), entry.getValue()));
            }
        }

        addChild(new Finally(new StatementBlock(newStatements)));
        changed();
    }

    private void addOldFlag(Map<ProgramVariable, ProgramVariable> oldFlags, ProgramVariable flag) {
        if (flag == null) {
            return;
        }

        oldFlags.put(flag,
            new LocationVariable(
                new ProgramElementName(
                    flag.getProgramElementName().toString() + "__BEFORE_FINALLY"),
                flag.getKeYJavaType()));
    }

    private void changed() {
        ExtList list = stack.peek();
        if (list.getFirst() != CHANGED) {
            list.addFirst(CHANGED);
        }
    }

    private void addChild(final SourceElement x) {
        stack.pop();
        ExtList list = stack.peek();
        list.add(x);
    }

    private abstract class DefaultAction {

        abstract ProgramElement createNewElement(ExtList changeList);

        private void addNewChild(final ExtList changeList) {
            addChild(createNewElement(changeList));
            changed();
        }

        public void doAction(final ProgramElement x) {
            final ExtList changeList = stack.peek();
            if (changeList.size() > 0 && changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
                addNewChild(changeList);
            } else {
                doDefaultAction(x);
            }
        }

    }

}
