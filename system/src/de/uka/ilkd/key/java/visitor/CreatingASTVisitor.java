// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.java.visitor;

import java.util.Stack;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.ClassInitializer;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.expression.operator.adt.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.util.ExtList;

/**
 * Walks through a java AST in depth-left-fist-order.
 */
public abstract class CreatingASTVisitor extends JavaASTVisitor {

    protected static final Boolean CHANGED = Boolean.TRUE;

    boolean preservesPositionInfo = true;

    /**  */
    //protected SimpleStackOfExtList stack = new SimpleStackOfExtList();
    protected Stack<ExtList> stack = new Stack<ExtList>();
    
    /**
     * create the CreatingASTVisitor
     * 
     * @param root
     *           the ProgramElement where to begin
     */
    public CreatingASTVisitor(ProgramElement root, 
                              boolean preservesPos,
                              Services services) {
        super(root, services);
	this.preservesPositionInfo = preservesPos;
    }

    public boolean preservesPositionInfo() {
        return preservesPositionInfo;
    }
    
    protected void walk(ProgramElement node) {
        ExtList l = new ExtList();
        l.add(node.getPositionInfo());
        stack.push(l);
        super.walk(node);
    }

    public String toString() {
        return stack.peek().toString();
    }

    /**
     * called if the program element x is unchanged
     */
    protected void doDefaultAction(SourceElement x) {
        addChild(x);
    }
    
    public void performActionOnAssert(Assert x) {
        ExtList changeList = stack.peek();
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            PositionInfo pos = changeList
                    .removeFirstOccurrence(PositionInfo.class);
            if (!preservesPositionInfo) {
                pos = PositionInfo.UNDEFINED;
            }
            Expression condition = changeList.removeFirstOccurrence(Expression.class);            
            Expression  message = changeList.removeFirstOccurrence(Expression.class);          
            
            addChild(new Assert(condition, message, pos));

            changed();
        } else {
            doDefaultAction(x);
        } 
    }

    public void performActionOnEmptyStatement(EmptyStatement x) {
        doDefaultAction(x);
    }

    public void performActionOnStatementBlock(final StatementBlock x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                StatementBlock newBlock = new StatementBlock(changeList);
                performActionOnBlockContract(x, newBlock);
                return newBlock;
            }
        };
        def.doAction(x);
    }

    protected void performActionOnBlockContract(final StatementBlock oldBlock, final StatementBlock newBlock) {
        //do nothing
    }
    
    protected void performActionOnLoopInvariant(LoopStatement oldLoop, 
                                                LoopStatement newLoop) {
        //do nothing
    }
    

    // eee
    public void performActionOnWhile(While x) {
        ExtList changeList = stack.peek();
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            PositionInfo pos = changeList.removeFirstOccurrence(PositionInfo.class);
            if (!preservesPositionInfo) {
		pos = PositionInfo.UNDEFINED;
	    }
	    Guard g = changeList.removeFirstOccurrence(Guard.class);
            Expression guard = g == null ? null : g.getExpression();
            Statement body = changeList.removeFirstOccurrence(Statement.class);
            
            While newX = new While(guard, body, pos);
            performActionOnLoopInvariant(x, newX);
            addChild(newX);

            changed();
        } else {
            doDefaultAction(x);
            performActionOnLoopInvariant(x, x);            
        }
    }

    // eee
    public void performActionOnDo(Do x) {
        ExtList changeList = stack.peek();
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            PositionInfo pos = changeList
                    .removeFirstOccurrence(PositionInfo.class);
            if (!preservesPositionInfo) {
		pos = PositionInfo.UNDEFINED;
	    }
            Statement body = changeList.removeFirstOccurrence(Statement.class);
            Guard g = changeList.removeFirstOccurrence(Guard.class);
            Expression guard = g == null ? null : g.getExpression();
            
            Do newX = new Do(guard, body, pos);
            performActionOnLoopInvariant(x, newX);
            addChild(newX);

            changed();
        } else {
            doDefaultAction(x);
            performActionOnLoopInvariant(x, x);
        }
    }

    public void performActionOnIf(If x) {

        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new If(changeList);
            }
        };
        def.doAction(x);

    }

    public void performActionOnThen(Then x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Then(changeList);
            }
        };
        def.doAction(x);
    }

    // eee
    public void performActionOnVariableSpecification(VariableSpecification x) {
        ExtList changeList = stack.peek();
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            PositionInfo pi = changeList.removeFirstOccurrence(PositionInfo.class);
	     
	    if (!preservesPositionInfo) {
		pi = PositionInfo.UNDEFINED;
	    }
            Expression expr = null;
            if (changeList.size() > 1) {
                expr = (Expression) changeList.get(1);
            }
            IProgramVariable pv = (IProgramVariable) changeList.get(0);
            addChild(new VariableSpecification(pv, x.getDimensions(), expr, pv
                    .getKeYJavaType(), pi));
            changed();
        } else {
            doDefaultAction(x);
        }

    }

    // eee
    public void performActionOnFieldReference(FieldReference x) {
        ExtList changeList = stack.peek();
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
	    
            PositionInfo pi = changeList.removeFirstOccurrence(PositionInfo.class);
	     
	    if (!preservesPositionInfo) {
		pi = PositionInfo.UNDEFINED;
	    }

            if (x.getReferencePrefix() != null) {
                final Expression field = (Expression) changeList.get(1);
                if (field instanceof ProgramVariable) {
                    addChild(new FieldReference((ProgramVariable) field,
                            (ReferencePrefix) changeList.get(0), pi));
                } else {
                    addChild(new FieldReference(
                            ((FieldReference) field).getProgramVariable(),
                            (ReferencePrefix) changeList.get(0), pi));
                }
            } else {
                addChild(new FieldReference(
                        (ProgramVariable) changeList.get(0), null, pi));
            }
            changed();
        } else {
            doDefaultAction(x);
        }

    }

    public void performActionOnSchematicFieldReference(
            SchematicFieldReference sfr) {
        performActionOnFieldReference(sfr);
    }

    // eee
    public void performActionOnMethodReference(MethodReference x) {
        ExtList changeList = stack.peek();
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();	    
	    
            PositionInfo pi = 
                changeList.removeFirstOccurrence(PositionInfo.class);
	     
	    if (!preservesPositionInfo) {
		pi = PositionInfo.UNDEFINED;
	    }
            
            ReferencePrefix rp = null;
            if (x.getReferencePrefix() != null) {
                rp = (ReferencePrefix) changeList.get(0);
            }
            changeList.remove(rp);
            MethodName name = changeList.get(MethodName.class);
            MethodReference mr = new MethodReference(changeList, name, rp, pi);
            addChild(mr);
            changed();
        } else {
            doDefaultAction(x);
        }
    }


    public void performActionOnTypeReference(final TypeReference x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new TypeRef(changeList, x.getKeYJavaType(), x
                        .getDimensions());
            }
        };
        def.doAction(x);
    }

    public void performActionOnElse(Else x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Else(changeList);
            }
        };
        def.doAction(x);
    }

    // eee
    public void performActionOnCase(Case x) {
        Expression e = null;
        ExtList changeList = stack.peek();
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            PositionInfo pi = changeList
                    .removeFirstOccurrence(PositionInfo.class);
            if (!preservesPositionInfo) {
                pi = PositionInfo.UNDEFINED;
            }
            if (x.getExpression() != null) {
                e = (Expression) changeList.removeFirst();
            }
            addChild(new Case(changeList, e, pi));
            changed();
        } else {
            doDefaultAction(x);
        }
    }

    public void performActionOnCatch(Catch x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Catch(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnThrow(Throw x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Throw(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnTry(Try x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Try(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnDefault(Default x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Default(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnFinally(Finally x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Finally(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnInstanceof(Instanceof x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Instanceof(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnBreak(Break x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Break(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnContinue(Continue x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Continue(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnFor(For x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                For newFor = new For(changeList);
                performActionOnLoopInvariant((For)pe, newFor);
                return newFor;
            }
        };
        def.doAction(x);
    }
    
    public void performActionOnEnhancedFor(EnhancedFor x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                EnhancedFor enhancedFor = new EnhancedFor(changeList);
                performActionOnLoopInvariant((EnhancedFor)pe, enhancedFor);
                return enhancedFor;
            }
        };
        def.doAction(x);
    }

    // eee
    public void performActionOnLabeledStatement(LabeledStatement x) {
        Label l = null;
        ExtList changeList = stack.peek();
        if (changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            PositionInfo pi = changeList
                    .removeFirstOccurrence(PositionInfo.class);
            if (!preservesPositionInfo) {
                pi = PositionInfo.UNDEFINED;
            }
            if (x.getLabel() != null) {
                l = (Label) changeList.removeFirst();
            }
            // bugfix: create an empty statement if the label body was removed
            if(changeList.get(Statement.class) == null)
        	changeList.add(new EmptyStatement());
            addChild(new LabeledStatement(changeList, l, pi));
            changed();
        } else {
            doDefaultAction(x);
        }
    }

    // eee
    public void performActionOnMethodFrame(MethodFrame x) {
        ExtList changeList = stack.peek();
        if (!changeList.isEmpty() && changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            PositionInfo pi = changeList
                    .removeFirstOccurrence(PositionInfo.class); //Methodframe cannot occur in original program
            
            if (!preservesPositionInfo()) {
                pi = PositionInfo.UNDEFINED;
            }
            
            if (x.getChildCount() == 3) {
                addChild(new MethodFrame((IProgramVariable) changeList.get(0),
                        (IExecutionContext) changeList.get(1),
                        (StatementBlock) changeList.get(2), pi));

            } else if (x.getChildCount() == 2) {
                addChild(new MethodFrame(null, (IExecutionContext) changeList
                        .get(0), (StatementBlock) changeList.get(1), pi));
            } else {
                throw new IllegalStateException(
                        "Methodframe has not allowed number of children.");
            }
            changed();
        } else {
            doDefaultAction(x);
        }
    }

    public void performActionOnMethodBodyStatement(final MethodBodyStatement x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new MethodBodyStatement(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnSynchronizedBlock(SynchronizedBlock x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new SynchronizedBlock(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnCopyAssignment(CopyAssignment x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new CopyAssignment(changeList);
            }
        };
        def.doAction(x);
    }
    
    public void performActionOnPreIncrement(PreIncrement x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new PreIncrement(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnPostIncrement(PostIncrement x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new PostIncrement(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnPlus(Plus x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Plus(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnTimes(Times x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Times(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnMinus(Minus x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Minus(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnEquals(Equals x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Equals(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnNotEquals(NotEquals x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new NotEquals(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnReturn(Return x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Return(changeList);
            }
        };
        def.doAction(x);
    }
    

    public void performActionOnLessThan(LessThan x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new LessThan(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnParenthesizedExpression(ParenthesizedExpression x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new ParenthesizedExpression(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnPassiveExpression(PassiveExpression x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new PassiveExpression(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnTypeCast(TypeCast x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new TypeCast(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnGreaterThan(GreaterThan x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new GreaterThan(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnBinaryAnd(BinaryAnd x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new BinaryAnd(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnBinaryOr(BinaryOr x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new BinaryOr(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnBinaryXOr(BinaryXOr x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new BinaryXOr(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnBinaryNot(BinaryNot x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new BinaryNot(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnBinaryAndAssignment(BinaryAndAssignment x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new BinaryAndAssignment(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnBinaryOrAssignment(BinaryOrAssignment x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new BinaryOrAssignment(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnBinaryXOrAssignment(BinaryXOrAssignment x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new BinaryXOrAssignment(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnDivideAssignment(DivideAssignment x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new DivideAssignment(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnMinusAssignment(MinusAssignment x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new MinusAssignment(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnModuloAssignment(ModuloAssignment x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new ModuloAssignment(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnPlusAssignment(PlusAssignment x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new PlusAssignment(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnPostDecrement(PostDecrement x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new PostDecrement(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnPreDecrement(PreDecrement x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new PreDecrement(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnShiftLeftAssignment(ShiftLeftAssignment x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new ShiftLeftAssignment(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnShiftRightAssignment(ShiftRightAssignment x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new ShiftRightAssignment(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnTimesAssignment(TimesAssignment x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new TimesAssignment(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnConditional(Conditional x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Conditional(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnUnsignedShiftRightAssignment(
            UnsignedShiftRightAssignment x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new UnsignedShiftRightAssignment(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnDivide(Divide x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Divide(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnNewArray(NewArray x) {
        DefaultAction def = new DefaultAction(x) {
            NewArray y = (NewArray) pe;

            ProgramElement createNewElement(ExtList children) {
                ArrayInitializer arrInit = children.get(ArrayInitializer.class);
                children.remove(arrInit);
                return new NewArray(children, y.getKeYJavaType(), arrInit, y
                        .getDimensions());
            }
        };
        def.doAction(x);
    }

    // ppp
    public void performActionOnNew(New x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList children) {
                PositionInfo pi = children.removeFirstOccurrence(PositionInfo.class);
                if (!preservesPositionInfo) {
                    pi = PositionInfo.UNDEFINED;
                }
                New y = (New) pe;
                ReferencePrefix rp = null;
                int rpPos = getPosition(y, y.getReferencePrefix());
                if (rpPos != -1) {
                    rp = (ReferencePrefix) children.get(rpPos);
                    children.remove(rpPos);
                }		
                return new New(children, rp, pi);
            }
        };
        def.doAction(x);
    }

    public void performActionOnLogicalNot(LogicalNot x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new LogicalNot(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnLogicalAnd(LogicalAnd x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new LogicalAnd(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnLogicalOr(LogicalOr x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new LogicalOr(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnModulo(Modulo x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Modulo(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnNegative(Negative x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Negative(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnPositive(Positive x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Positive(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnShiftLeft(ShiftLeft x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new ShiftLeft(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnShiftRight(ShiftRight x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new ShiftRight(changeList);
            }
        };
        def.doAction(x);
    }

    // ppp
    public void performActionOnArrayReference(ArrayReference x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList children) {                
                PositionInfo pos = children
                .removeFirstOccurrence(PositionInfo.class);
                ArrayReference y = (ArrayReference) pe;
                ReferencePrefix prefix = null;
                int prefixPos = getPosition(y, y.getReferencePrefix());
                if (prefixPos != -1) {
                    prefix = (ReferencePrefix) children.get(prefixPos);
                    children.remove(prefixPos);
                }	
                if (!preservesPositionInfo) {
		    pos = PositionInfo.UNDEFINED;
		}
                return new ArrayReference(children, prefix, pos);
            }
        };
        def.doAction(x);
    }

    public void performActionOnMetaClassReference(MetaClassReference x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new MetaClassReference(changeList);
            }
        };
        def.doAction(x);
    }

    // ppp
    public void performActionOnSuperConstructorReference(
            SuperConstructorReference x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList children) {
                PositionInfo pos = children
                        .removeFirstOccurrence(PositionInfo.class);
                SuperConstructorReference y = (SuperConstructorReference) pe;
                ReferencePrefix prefix = null;
                int prefixPos = getPosition(y, y.getReferencePrefix());
                if (prefixPos != -1) {
                    prefix = (ReferencePrefix) children.get(prefixPos);
                    children.remove(prefixPos);
                }
		
                if (!preservesPositionInfo) {
		    pos = PositionInfo.UNDEFINED;
		} 
                
                return new SuperConstructorReference(children, prefix, pos);
            }
        };
        def.doAction(x);
    }

    public void performActionOnThisConstructorReference(
            ThisConstructorReference x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new ThisConstructorReference(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnExecutionContext(ExecutionContext x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {        	
        	return new ExecutionContext(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnSuperReference(final SuperReference x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new SuperReference(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnThisReference(final ThisReference x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new ThisReference(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnArrayLengthReference(ArrayLengthReference x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new ArrayLengthReference(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnSwitch(Switch x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Switch(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnClassInitializer(ClassInitializer x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new ClassInitializer(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnArrayInitializer(final ArrayInitializer x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new ArrayInitializer(changeList, x.getKeYJavaType(services, null));
            }
        };
        def.doAction(x);
    }

    public void performActionOnPackageReference(PackageReference x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new PackageReference(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnPackageSpecification(PackageSpecification x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new PackageSpecification(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnLessOrEquals(LessOrEquals x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new LessOrEquals(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnGreaterOrEquals(GreaterOrEquals x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new GreaterOrEquals(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnLocalVariableDeclaration(
            LocalVariableDeclaration x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {		
                return new LocalVariableDeclaration(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnParameterDeclaration(ParameterDeclaration x) {
        DefaultAction def = new ParameterDeclarationAction(x);
        def.doAction(x);
    }

    private class ParameterDeclarationAction extends DefaultAction {
        ParameterDeclaration x;

        ParameterDeclarationAction(ParameterDeclaration x) {
            super(x);
            this.x = x;
        }

        ProgramElement createNewElement(ExtList changeList) {
            return new ParameterDeclaration(changeList, x
                    .parentIsInterfaceDeclaration(), x.isVarArg());
        }
    }

    // eee
    public void performActionOnForUpdates(final ForUpdates x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
		PositionInfo pi;
                if (!preservesPositionInfo) {
		    pi = PositionInfo.UNDEFINED;
		} else {
		    pi = changeList.removeFirstOccurrence(PositionInfo.class);
		}
                return new ForUpdates(changeList, pi);
            }
        };
        def.doAction(x);
    }

    public void performActionOnGuard(Guard x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Guard(changeList);
            }
        };
        def.doAction(x);
    }

    public void performActionOnLoopInit(LoopInit x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
		final PositionInfo pi; 
                if (!preservesPositionInfo) {
		    pi = PositionInfo.UNDEFINED;
		} else {                    
		    pi = changeList.removeFirstOccurrence(PositionInfo.class);
		}
                return new LoopInit(changeList, pi);
            }
        };
        def.doAction(x);
    }
    
    
    @Override
    public void performActionOnSingleton(Singleton x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Singleton(changeList);
            }
        };
        def.doAction(x);	
    }    
    
    
    @Override
    public void performActionOnSetUnion(SetUnion x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new SetUnion(changeList);
            }
        };
        def.doAction(x);	
    }
    
    
    @Override
    public void performActionOnIntersect(Intersect x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new Intersect(changeList);
            }
        };
        def.doAction(x);	
    }
    
    @Override    
    public void performActionOnSetMinus(SetMinus x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new SetMinus(changeList);
            }
        };
        def.doAction(x);	
    }
    
    @Override
    public void performActionOnAllFields(AllFields x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new AllFields(changeList);
            }
        };
        def.doAction(x);	
    }
    

    @Override
    public void performActionOnSeqSingleton(SeqSingleton x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new SeqSingleton(changeList);
            }
        };
        def.doAction(x);	
    }
    
    
    @Override
    public void performActionOnSeqConcat(SeqConcat x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new SeqConcat(changeList);
            }
        };
        def.doAction(x);	
    } 
    
    @Override
    public void performActionOnSeqReverse(SeqReverse x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new SeqReverse(changeList);
            }
        };
        def.doAction(x);        
    } 
    
    @Override
    public void performActionOnDLEmbeddedExpression(final DLEmbeddedExpression x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new DLEmbeddedExpression(x.getFunctionSymbol(), changeList);
            }
        };
        def.doAction(x);        
    } 
    
    
    @Override
    public void performActionOnSeqSub(SeqSub x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new SeqSub(changeList);
            }
        };
        def.doAction(x);	
    }     
    
    @Override
    public void performActionOnSeqLength(SeqLength x) {
        DefaultAction def = new DefaultAction(x) {
            ProgramElement createNewElement(ExtList changeList) {
                return new SeqLength(changeList);
            }
        };
        def.doAction(x);        
    }

    /**
     * returns the position of pe2 in the virtual child array of pe1
     */
    protected static int getPosition(NonTerminalProgramElement pe1,
            ProgramElement pe2) {
        int n = pe1.getChildCount();
        int i = 0;
        while ((i < n) && (pe1.getChildAt(i) != pe2))
            i++;
        return (i == n) ? -1 : i;
    }

    protected void changed() {
        ExtList list = stack.peek();
        if (list.isEmpty() || list.getFirst() != CHANGED) {
            list.addFirst(CHANGED);
        }
    }

    protected void addToTopOfStack(SourceElement x) {
        if (x != null) {
            ExtList list = stack.peek();
            list.add(x);
        }
    }

    protected void addChild(SourceElement x) {
        stack.pop();
        addToTopOfStack(x);
    }

    protected void addChildren(ImmutableArray<ProgramElement> arr) {
        stack.pop();
        for (int i = 0, sz = arr.size(); i < sz; i++) {
            addToTopOfStack(arr.get(i));
        }
    }

    protected abstract class DefaultAction {
        abstract ProgramElement createNewElement(ExtList changeList);

        protected ProgramElement pe;
     
        protected DefaultAction(ProgramElement pe) {
            this.pe = pe;
        }

        protected void addNewChild(ExtList changeList) {
            addChild(createNewElement(changeList));
            changed();
        }

        public void doAction(ProgramElement x) {
            ExtList changeList = stack.peek();
            if (changeList.size() == 0) {
                doDefaultAction(x);
                return;
            }
            if (changeList.getFirst() == CHANGED) {
                changeList.removeFirst();
                if (!preservesPositionInfo) {
		    changeList.removeFirstOccurrence(PositionInfo.class);
		}
                addNewChild(changeList);
            } else {
                doDefaultAction(x);
            }
        }
    }
}
