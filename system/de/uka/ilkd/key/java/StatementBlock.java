// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclarationContainer;
import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ArrayOfProgramPrefix;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.util.ExtList;

/**
 *    Statement block.
 * taken from COMPOST and changed to achieve an immutable structure
 */

public class StatementBlock extends JavaStatement
    implements StatementContainer, TypeDeclarationContainer,
               VariableScope, TypeScope, ProgramPrefix {

    /**
     *      Body.
     */
    private final ArrayOfStatement body;

    
    /**
     * contains all program prefix elements below and including itself
     */
    private final ArrayOfProgramPrefix prefixElementArray;

    private PosInProgram firstActiveChildPos = null;
    
    
    public StatementBlock() {
	body = new ArrayOfStatement();
        prefixElementArray = new ArrayOfProgramPrefix(this);
    }

    /**
     *      Statement block.
     *  @param children an ExtList that contains the children
     */
    
    public StatementBlock(ExtList children) {
        super(children);
        body = new
            ArrayOfStatement((Statement[])children.collect(Statement.class));
        
        prefixElementArray = computePrefixElements(body);
    }

    public StatementBlock(ArrayOfStatement as) {
	body = as;
        prefixElementArray = computePrefixElements(body);
    }
        

    public StatementBlock(Statement as) {
	this(new ArrayOfStatement(as));
    }

    public StatementBlock(Statement[] body) {
	this(new ArrayOfStatement(body));
    }

    private ArrayOfProgramPrefix computePrefixElements(ArrayOfStatement b) {
        return computePrefixElements(b,0,this);
    }

    /** computes the prefix elements for the given array of statment block */
    public static ArrayOfProgramPrefix computePrefixElements(ArrayOfStatement b, 
            int offset, ProgramPrefix current) {
        final ProgramPrefix[] pp;

        if (b.size()>0 && b.getStatement(0) instanceof ProgramPrefix) {
            final ProgramPrefix prefixElement = (ProgramPrefix) b.getStatement(0);
            
            final int prefixLength = 
                ((ProgramPrefix)b.getStatement(0)).getPrefixLength();
            pp = new ProgramPrefix[prefixLength + 1];            
            prefixElement.getPrefixElements().arraycopy(offset, pp, 1, prefixLength);            
        } else {
            pp = new ProgramPrefix[1];            
        }                
        pp[0] = current;
        return new ArrayOfProgramPrefix(pp);
    }

   
    
    /**
     *      Get body.
     *      @return the statement array wrapper.
     */

    public ArrayOfStatement getBody() {
        return body;
    }

    public boolean isEmpty() {
	return body.size() == 0;
    }


    /**
     *      Returns the number of children of this node.
     *      @return an int giving the number of children of this node
     */
    
    public int getChildCount() {
        return body.size();
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
        if (body != null) {
            return body.getStatement(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get the number of statements in this container.
     *      @return the number of statements.
     */

    public int getStatementCount() {
        return body.size();
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
        if (body != null) {
            return body.getStatement(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     *      Get the number of type declarations in this container.
     *      @return the number of type declarations.
     */

    public int getTypeDeclarationCount() {
        int count = 0;
        if (body != null) {
            for (int i = body.size() - 1; i >= 0; i -= 1) {
                if (body.getStatement(i) instanceof TypeDeclaration) {
                    count += 1;
                }
            }
        }
        return count;
    }

    /*
      Return the type declaration at the specified index in this node's
      "virtual" type declaration array.
      @param index an index for a type declaration.
      @return the type declaration with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */

    public TypeDeclaration getTypeDeclarationAt(int index) {
        if (body != null) {
            int s = body.size();
            for (int i = 0; i < s && index >= 0; i++) {
                Statement st = body.getStatement(i);
                if (st instanceof TypeDeclaration) {
                    if (index == 0) {
                        return (TypeDeclaration)st;
                    }
                    index -= 1;
                }
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnStatementBlock(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printStatementBlock(this);
    }


    public SourceElement getFirstElement() {
        if (isEmpty()) return this;
        final SourceElement e = getBody().getStatement(0);
        return (e instanceof StatementBlock) ? e.getFirstElement() : e;
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
            firstActiveChildPos = isEmpty() ? PosInProgram.TOP : PosInProgram.TOP.down(0);
        }
        return firstActiveChildPos;
    }
 



}
