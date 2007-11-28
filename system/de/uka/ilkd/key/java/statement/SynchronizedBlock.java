// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ArrayOfProgramPrefix;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.util.ExtList;

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
    
    private final ArrayOfProgramPrefix prefixElementArray;
    
    private PosInProgram firstActiveChildPos = null;

    /**
 *      Synchronized block.
 *      @param body a statement block.
     */

    public SynchronizedBlock(StatementBlock body) {
        this.body=body;
	this.expression=null;
        prefixElementArray = computePrefix(body);
        
    }

    /**
 *      Synchronized block.
 *      @param e an expression.
 *      @param body a statement block.
     */

    public SynchronizedBlock(Expression e, StatementBlock body) {
        expression=e;
        this.body=body;
        prefixElementArray = computePrefix(body);
        
    }

    /**
 *      Synchronized block.
 *      @param children a list with all children
     */

    public SynchronizedBlock(ExtList children) {
        super(children);
	expression = (Expression)children.get(Expression.class);
	body = (StatementBlock)children.get(StatementBlock.class);
        prefixElementArray = computePrefix(body);        
    }



    private ArrayOfProgramPrefix computePrefix(StatementBlock b) {
        return StatementBlock.
           computePrefixElements(b.getBody(), 0, this);                
}

    public int getPrefixLength() {        
        return prefixElementArray.size();
    }

    public ProgramPrefix getPrefixElementAt(int i) {       
        return prefixElementArray.getProgramPrefix(i);
    }

    public ArrayOfProgramPrefix getPrefixElements() {
        return prefixElementArray;
    }
    
    
    public PosInProgram getFirstActiveChildPos() {
        if (firstActiveChildPos == null) {
            firstActiveChildPos = getStatementCount() == 0 ? PosInProgram.TOP : PosInProgram.TOP.down(1);
        } 
        return firstActiveChildPos;
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
