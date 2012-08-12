package de.uka.ilkd.key.java.visitor;

import java.util.*;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.util.ExtList;

public class OuterBreakContinueAndReturnReplacer extends JavaASTVisitor {

    protected static final Boolean CHANGED = Boolean.TRUE;

    private final Break breakOut;
    private final Map<Label, ProgramVariable> breakFlags;
    private final Map<Label, ProgramVariable> continueFlags;
    private final ProgramVariable returnFlag;
    private final ProgramVariable returnValue;

    private final Stack<ExtList> stack = new Stack<ExtList>();
    private final Stack<Label> labels = new Stack<Label>();
    private final Stack<MethodFrame> frames = new Stack<MethodFrame>();
    private int loopAndSwitchCascadeDepth;

    private StatementBlock result;

    public OuterBreakContinueAndReturnReplacer(StatementBlock block,
                                               Label breakOutLabel,
                                               Map<Label, ProgramVariable> breakFlags,
                                               Map<Label, ProgramVariable> continueFlags,
                                               ProgramVariable returnFlag,
                                               ProgramVariable returnValue,
                                               Services services)
    {
        super(block, services);
        breakOut = new Break(breakOutLabel);
        this.breakFlags = breakFlags;
        this.continueFlags = continueFlags;
        this.returnFlag = returnFlag;
        this.returnValue = returnValue;
    }

    public StatementBlock replace()
    {
        start();
        return result;
    }

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

    protected void walk(ProgramElement node) {
        stack.push(new ExtList());
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

    public String toString() {
        return stack.peek().toString();
    }

    protected void doDefaultAction(SourceElement x) {
        addChild(x);
    }


    public void performActionOnBreak(final Break x) {
        performActionOnJump(x, breakFlags);
    }


    public void performActionOnContinue(final Continue x) {
        performActionOnJump(x, continueFlags);
    }


    private void performActionOnJump(final LabelJumpStatement x, Map<Label, ProgramVariable> flags) {
        if (isJumpToOuterLabel(x)) {
            final ProgramVariable flag = flags.get(x.getLabel());
            final Statement assign = KeYJavaASTFactory.assign(flag, BooleanLiteral.TRUE);
            final Statement[] statements = new Statement[] {assign, breakOut};
            addChild(new StatementBlock(statements));
            changed();
        }
        else {
            doDefaultAction(x);
        }
    }


    private boolean isJumpToOuterLabel(final LabelJumpStatement x) {
        return loopAndSwitchCascadeDepth == 0 && x.getProgramElementName() == null
                || x.getLabel() != null && labels.search(x.getLabel()) == -1
                /*|| labels.contains(x.getProgramElementName())*/;
    }


    public void performActionOnReturn(Return x) {
        if (frames.empty()) {
            ExtList changeList = stack.peek();
            if (!changeList.isEmpty() && changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
            }
            Statement assignFlag = KeYJavaASTFactory.assign(returnFlag, BooleanLiteral.TRUE);
            final Statement[] statements;
            if (returnValue == null) {
                statements = new Statement[] {assignFlag, breakOut};
            }
            else {
                Statement assignValue = KeYJavaASTFactory.assign(returnValue, x.getExpression());
                statements = new Statement[] {assignFlag, assignValue, breakOut};
            }
            addChild(new StatementBlock(statements));
            changed();
        }
        else {
            //frames.pop();
            doDefaultAction(x);
        }
    }


    public void performActionOnLocalVariableDeclaration(LocalVariableDeclaration x) {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(ExtList changeList) {
                return new LocalVariableDeclaration(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnStatementBlock(StatementBlock x) {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(ExtList changeList) {
                return new StatementBlock(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnWhile(While x) {
        ExtList changeList = stack.peek();
        if (!changeList.isEmpty() && changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            Expression guard = ((Guard) changeList.removeFirst()).getExpression();
            Statement body = (Statement) (changeList.isEmpty() ? null : changeList.removeFirst());
            addChild(new While(guard, body, x.getPositionInfo()));
            changed();
        }
        else {
            doDefaultAction(x);
        }
    }

    public void performActionOnFor(For x) {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(ExtList changeList) {
                return new For(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnEnhancedFor(EnhancedFor x) {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(ExtList changeList) {
                return new EnhancedFor(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnDo(Do x) {
        ExtList changeList = stack.peek();
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            Expression guard = (Expression) changeList.removeFirst();
            Statement body = (Statement) (changeList.isEmpty() ? null : changeList.removeFirst());
            addChild(new Do(guard, body, x.getPositionInfo()));
            changed();
        }
        else {
            doDefaultAction(x);
        }
    }


    public void performActionOnIf(If x) {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(ExtList changeList) {
                return new If(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnSwitch(Switch x) {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(ExtList changeList) {
                return new Switch(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnTry(Try x) {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(ExtList changeList) {
                return new Try(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnLabeledStatement(LabeledStatement x) {
        Label l = null;
        ExtList changeList = stack.peek();
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            if (x.getLabel() != null) {
                l = (Label) changeList.removeFirst();
            }
            addChild(new LabeledStatement(changeList, l, x.getPositionInfo()));
            changed();
        }
        else {
            doDefaultAction(x);
        }
    }

    public void performActionOnMethodFrame(MethodFrame x) {
        ExtList changeList = stack.peek();
        if (!changeList.isEmpty() && changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            if (x.getChildCount() == 3) {
                addChild(new MethodFrame((IProgramVariable) changeList.get(0),
                                (IExecutionContext) changeList.get(1),
                                (StatementBlock) changeList.get(2),
                                PositionInfo.UNDEFINED));

            }
            else if (x.getChildCount() == 2) {
                addChild(new MethodFrame(null,
                                (IExecutionContext) changeList.get(0),
                                (StatementBlock) changeList.get(1),
                                PositionInfo.UNDEFINED));
            }
            else {
                throw new IllegalStateException("Method-frame has wrong number of children.");
            }
            changed();
        }
        else {
            doDefaultAction(x);
        }
    }


    public void performActionOnSynchronizedBlock(SynchronizedBlock x) {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(ExtList changeList) {
                return new SynchronizedBlock(changeList);
            }
        };
        def.doAction(x);
    }


    public void performActionOnCopyAssignment(CopyAssignment x) {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(ExtList changeList) {
                return new CopyAssignment(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnThen(Then x) {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(ExtList changeList) {
                return new Then(changeList);
            }
        };
        def.doAction(x);
    }


    public void performActionOnElse(Else x) {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(ExtList changeList) {
                return new Else(changeList);
            }
        };
        def.doAction(x);
    }


    public void performActionOnCase(Case x) {
        Expression e = null;
        ExtList changeList = stack.peek();
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            if (x.getExpression() != null) {
                e = (Expression) changeList.removeFirst();
            }
            addChild(new Case(changeList, e, x.getPositionInfo()));
            changed();
        }
        else {
            doDefaultAction(x);
        }
    }


    public void performActionOnCatch(Catch x) {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(ExtList changeList) {
                return new Catch(changeList);
            }
        };
        def.doAction(x);
    }


    public void performActionOnDefault(Default x) {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(ExtList changeList) {
                return new Default(changeList);
            }
        };
        def.doAction(x);
    }


    public void performActionOnFinally(Finally x) {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(ExtList changeList) {
                return new Finally(changeList);
            }
        };
        def.doAction(x);
    }


    protected void changed() {
        ExtList list = stack.peek();
        if (list.getFirst() != CHANGED) {
            list.addFirst(CHANGED);
        }
    }

    protected void addChild(SourceElement x) {
        stack.pop();
        ExtList list = stack.peek();
        list.add(x);
    }

    private abstract class DefaultAction {
        abstract ProgramElement createNewElement(ExtList changeList);

        private void addNewChild(ExtList changeList) {
            addChild(createNewElement(changeList));
            changed();
        }

        public void doAction(ProgramElement x) {
            ExtList changeList = stack.peek();
            if (changeList.size() > 0 && changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
                addNewChild(changeList);
            } else {
                doDefaultAction(x);
            }
        }
    }
}