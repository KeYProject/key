package de.uka.ilkd.key.java.visitor;

import java.util.Stack;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.statement.Break;
import de.uka.ilkd.key.java.statement.Case;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.Continue;
import de.uka.ilkd.key.java.statement.Default;
import de.uka.ilkd.key.java.statement.Do;
import de.uka.ilkd.key.java.statement.Else;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.Finally;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.Guard;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.Switch;
import de.uka.ilkd.key.java.statement.SynchronizedBlock;
import de.uka.ilkd.key.java.statement.Then;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.rule.LoopContractApplyHeadRule;
import de.uka.ilkd.key.speclang.SimpleLoopContract;

/**
 * This replaces all breaks and continues in a loop with {@code break l}, where {@code l} is a
 * specified label. It is used in the transformation of a for loop to a while loop.
 * 
 * @see LoopContractApplyHeadRule
 * @see SimpleLoopContract
 */
public class InnerBreakAndContinueReplacer extends JavaASTVisitor {

    protected static final Boolean CHANGED = Boolean.TRUE;

    private final Break breakOuter;
    private final Break breakInner;

    private final Stack<ExtList> stack = new Stack<ExtList>();
    private final Stack<Label> loopLabels = new Stack<Label>();
    private final Stack<MethodFrame> frames = new Stack<MethodFrame>();
    private int loopAndSwitchCascadeDepth;

    private StatementBlock result;

    public InnerBreakAndContinueReplacer(final StatementBlock block,
                                               final Iterable<Label> loopLabels,
                                               final Label breakLabel,
                                               final Label continueLabel,
                                               final Services services)
    {
        super(block, services);
        for (Label label : loopLabels) {
            this.loopLabels.add(label);
        }
        
        this.breakOuter = new Break(breakLabel);
        this.breakInner = new Break(continueLabel);
    }

    public StatementBlock replace()
    {
        start();
        return result;
    }

    public void start()
    {
        loopAndSwitchCascadeDepth = 0;
        stack.push(new ExtList());
        super.start();
        ExtList el = stack.peek();
        int i = (el.get(0) == CHANGED ? 1 : 0);
        result = (StatementBlock) el.get(i);
    }

    public StatementBlock getResult()
    {
        return result;
    }

    protected void walk(final ProgramElement node)
    {
        if (node.getPositionInfo() != PositionInfo.UNDEFINED) {
           stack.push(new ExtList(new Object[] {node.getPositionInfo()}));
        }
        else {
           stack.push(new ExtList());
        }
        if (node instanceof LoopStatement || node instanceof Switch) {
            loopAndSwitchCascadeDepth++;
        }
        if (node instanceof MethodFrame) {
            frames.push((MethodFrame) node);
        }
        super.walk(node);
        if (node instanceof MethodFrame) {
            frames.pop();
        }
        if (node instanceof LoopStatement || node instanceof Switch) {
            loopAndSwitchCascadeDepth--;
        }
    }

    public String toString()
    {
        return stack.peek().toString();
    }

    protected void doDefaultAction(final SourceElement x)
    {
        addChild(x);
    }

    public void performActionOnContinue(final Continue x)
    {
        if (loopAndSwitchCascadeDepth == 0 && x.getProgramElementName() == null
                || x.getLabel() != null && loopLabels.contains(x.getLabel())) {
            addChild(breakInner);
            changed();
        }
        else {
            doDefaultAction(x);
        }
    }

    public void performActionOnBreak(final Break x)
    {
        if (loopAndSwitchCascadeDepth == 0 && x.getProgramElementName() == null
                || x.getLabel() != null && loopLabels.contains(x.getLabel())) {
            addChild(breakOuter);
            changed();
        }
        else {
            doDefaultAction(x);
        }
    }


    public void performActionOnLocalVariableDeclaration(final LocalVariableDeclaration x)
    {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(final ExtList changeList) {
                return new LocalVariableDeclaration(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnStatementBlock(final StatementBlock x)
    {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(final ExtList changeList) {
                return new StatementBlock(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnWhile(final While x)
    {
        final ExtList changeList = stack.peek();
        if (!changeList.isEmpty() && changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            Expression guard = ((Guard) changeList.removeFirst()).getExpression();
            Statement body = (Statement) (changeList.isEmpty() ? null : changeList.removeFirst());
            While newLoop = new While(guard, body, x.getPositionInfo());
            services.getSpecificationRepository().copyLoopInvariant(x, newLoop);
            addChild(newLoop);
            changed();
        }
        else {
            doDefaultAction(x);
        }
    }

    public void performActionOnFor(final For x)
    {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(final ExtList changeList) {
                For newLoop = new For(changeList);
                services.getSpecificationRepository().copyLoopInvariant(x, newLoop);
                return newLoop;
            }
        };
        def.doAction(x);
    }

    public void performActionOnEnhancedFor(final EnhancedFor x)
    {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(final ExtList changeList) {
                EnhancedFor newLoop = new EnhancedFor(changeList);
                services.getSpecificationRepository().copyLoopInvariant(x, newLoop);
                return newLoop;
            }
        };
        def.doAction(x);
    }

    public void performActionOnDo(final Do x)
    {
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
        }
        else {
            doDefaultAction(x);
        }
    }

    public void performActionOnIf(final If x)
    {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(final ExtList changeList) {
                return new If(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnSwitch(final Switch x)
    {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(final ExtList changeList) {
                return new Switch(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnTry(final Try x)
    {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(final ExtList changeList) {
                return new Try(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnLabeledStatement(final LabeledStatement x)
    {
        Label l = null;
        final ExtList changeList = stack.peek();
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

    public void performActionOnMethodFrame(final MethodFrame x)
    {
        final ExtList changeList = stack.peek();
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

    public void performActionOnSynchronizedBlock(final SynchronizedBlock x)
    {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(final ExtList changeList) {
                return new SynchronizedBlock(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnCopyAssignment(final CopyAssignment x)
    {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(final ExtList changeList) {
                return new CopyAssignment(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnThen(final Then x)
    {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(final ExtList changeList) {
                return new Then(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnElse(final Else x)
    {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(final ExtList changeList) {
                return new Else(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnCase(final Case x)
    {
        Expression e = null;
        final ExtList changeList = stack.peek();
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

    public void performActionOnCatch(final Catch x)
    {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(final ExtList changeList) {
                return new Catch(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnDefault(final Default x)
    {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(final ExtList changeList) {
                return new Default(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnFinally(final Finally x)
    {
        DefaultAction def = new DefaultAction() {
            ProgramElement createNewElement(final ExtList changeList) {
                return new Finally(changeList);
            }
        };
        def.doAction(x);
    }

    private void changed()
    {
        ExtList list = stack.peek();
        if (list.getFirst() != CHANGED) {
            list.addFirst(CHANGED);
        }
    }

    private void addChild(final SourceElement x)
    {
        stack.pop();
        ExtList list = stack.peek();
        list.add(x);
    }

    private abstract class DefaultAction {

        abstract ProgramElement createNewElement(ExtList changeList);

        private void addNewChild(final ExtList changeList)
        {
            addChild(createNewElement(changeList));
            changed();
        }

        public void doAction(final ProgramElement x)
        {
            final ExtList changeList = stack.peek();
            if (changeList.size() > 0 && changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
                addNewChild(changeList);
            }
            else {
                doDefaultAction(x);
            }
        }

    }

}