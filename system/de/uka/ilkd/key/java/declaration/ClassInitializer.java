// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.modifier.Static;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Class initializer.
 *  @author <TT>AutoDoc</TT>
 */

public class ClassInitializer extends JavaDeclaration implements MemberDeclaration, StatementContainer {



    /**
 *      Body.
     */

    protected final StatementBlock body;

    /**
 *      Class initializer.
     */

    public ClassInitializer() {
	super((Modifier[])null);
	body=null;
    }


    /**
 *      Class initializer.
 *      @param modifier a static.
 *      @param body a statement block.
     */

    public ClassInitializer(Static modifier, StatementBlock body) {
	super(new Modifier[]{modifier});
	this.body=body;
    }

    /**
     *  Class initializer.
     *  @param children list with all children. May include: a
     * 	StatementBlock (taken as body of the ClassInitialiyer), 
     * 	several Modifier (taken as modifiers of the declaration), a Comment
     */
    public ClassInitializer(ExtList children) {
        super(children);
	body=(StatementBlock)children.get(StatementBlock.class);
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

    /**
 *      Returns the number of children of this node.
 *      @return an int giving the number of children of this node
    */

    public int getChildCount() {
        int result = 0;
        if (modArray != null) result += modArray.size();
        if (body != null) result++;
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
        int len;
        if (modArray != null) {
            len = modArray.size();
            if (len > index) {
                return modArray.getModifier(index);
            }
            index -= len;
        }
        if (body != null) {
            if (index == 0) return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /** A binary class initializer does not occur. */

    public boolean isBinary() {
        return false;
    }


    /**
     * Initializers are never public.
     */

    public boolean isPublic() {
        return false;
    }

    /**
     * Initializers are never protected.
     */

    public boolean isProtected() {
        return false;
    }

    /**
     * Initializers are never private (at least not explicitly).
     */

    public boolean isPrivate() {
        return false;
    }

    /**
     * Initializers are never strictfp.
     */

    public boolean isStrictFp() {
        return false;
    }

    /**
     * Test whether the declaration is static.
     */

    public boolean isStatic() {
        return modArray != null && modArray.size()!=0;
    }

    public SourceElement getLastElement() {
        return body;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnClassInitializer(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printClassInitializer(this);
    }
}
