// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.statement;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ExpressionContainer;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.ProgramPrefixUtil;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MetaClassReference;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 *  Synchronized block.
 */

public class SynchronizedBlock extends JavaStatement 
    implements StatementContainer, ExpressionContainer, ProgramPrefix {

    /**
 *      Expression.
     */

    protected final Expression expression;

    /**
 *      Body.
     */

    protected final StatementBlock body;

    private final MethodFrame innerMostMethodFrame;

    private final int prefixLength;
    
   
    
    /**
 *      Synchronized block.
 *      @param body a statement block.
     */

    public SynchronizedBlock(StatementBlock body) {
        this.body=body;
	this.expression=null;
    ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
    prefixLength = info.getLength();
    innerMostMethodFrame = info.getInnerMostMethodFrame();

    }

    /**
 *      Synchronized block.
 *      @param e an expression.
 *      @param body a statement block.
     */

    public SynchronizedBlock(Expression e, StatementBlock body) {
        expression=e;
        this.body=body;
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
        innerMostMethodFrame = info.getInnerMostMethodFrame();

    }

    /**
 *      Synchronized block.
 *      @param children a list with all children
     */

    public SynchronizedBlock(ExtList children) {
        super(children);
	expression = children.get(Expression.class);
	body = children.get(StatementBlock.class);
    ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
    prefixLength = info.getLength();
    innerMostMethodFrame = info.getInnerMostMethodFrame();

    }

    @Override
    public boolean hasNextPrefixElement() {
        return !body.isEmpty() && body.getStatementAt(0) instanceof ProgramPrefix;
    }

    @Override
    public ProgramPrefix getNextPrefixElement() {
        if (hasNextPrefixElement()) {
            return (ProgramPrefix) body.getStatementAt(0);
        } else {
            throw new IndexOutOfBoundsException("No next prefix element " + this);
        }
    }
    
    @Override
    public ProgramPrefix getLastPrefixElement() {
        return hasNextPrefixElement() ? getNextPrefixElement().getLastPrefixElement() : 
            this;
    }
    
    @Override
    public int getPrefixLength() {
        return prefixLength;
    }

    @Override
    public MethodFrame getInnerMostMethodFrame() {
        return innerMostMethodFrame;
    }

    @Override
    public ImmutableArray<ProgramPrefix> getPrefixElements() {
        return StatementBlock.computePrefixElements(body.getBody(), this);
    }    

    /**
     * The method checks whether the expression in the synchronized
     * prefix is either a local variable or a meta class reference
     * (as local variables of this type are not supported by KeY,
     * see return value for
     * {@link MetaClassReference#getKeYJavaType(Services, ExecutionContext)}.
     * @return true iff the above stated condition holds.
     */
    private boolean expressionWithoutSideffects() {
        return (expression instanceof ProgramVariable
                    && !((ProgramVariable)expression).isMember())
                || (expression instanceof MetaClassReference);
    }

    public PosInProgram getFirstActiveChildPos() {
        return getStatementCount() == 0 ?
                PosInProgram.TOP : (expressionWithoutSideffects() ?
                        PosInProgram.TOP.down(getChildCount()-1).down(0) : PosInProgram.ONE);
    }
    
    /**
 *      Get the number of expressions in this container.
 *      @return the number of expressions.
     */

    public int getExpressionCount() {
        return (expression != null) ? 1 : 0;
    }

    /*
      Return the expression at the specified index in this node's
      "virtual" expression array.
      @param index an index for an expression.
      @return the expression with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */

    public Expression getExpressionAt(int index) {
        if (expression != null && index == 0) {
            return expression;
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    /**
 *      Get expression.
 *      @return the expression.
     */

    public Expression getExpression() {
        return expression;
    }

    /**
 *      Returns the number of children of this node.
 *      @return an int giving the number of children of this node
    */

    public int getChildCount() {
        int result = 0;
        if (expression != null) result++;
        if (body       != null) result++;
        return result;
    }

    /**
 *      Returns the child at the specified index in this node's "virtual"
 *      child array
 *      @param index an index into this node's "virtual" child array
 *      @return the program element at the given position
 *      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
 *                 of bounds
    */

    public ProgramElement getChildAt(int index) {       
        if (expression != null) {
            if (index == 0) return expression;
            index--;
        }
        if (body != null) {
            if (index == 0) return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
 *      Get body.
 *      @return the statement block.
     */

    public StatementBlock getBody() {
        return body;
    }


    /**
 *      Get the number of statements in this container.
 *      @return the number of statements.
     */

    public int getStatementCount() {
        return (body != null) ? 1 : 0;
    }

    /*
      Return the statement at the specified index in this node's
      "virtual" statement array.
      @param index an index for a statement.
      @return the statement with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */

    public Statement getStatementAt(int index) {
        if (body != null && index == 0) {
            return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }
    


    public SourceElement getFirstElement() {
        return body.getFirstElement();
    }


    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnSynchronizedBlock(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printSynchronizedBlock(this);
    }
}