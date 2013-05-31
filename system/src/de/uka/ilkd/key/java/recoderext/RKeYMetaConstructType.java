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


// This file is taken from the RECODER library, which is protected by the LGPL,
// and modified.
/** This class is part of the AST RECODER builds when it parses and resolves Java
 * programs with meta constructs and schema variables. It is transformed by 
 * SchemaRecoder2KeY
 * to a subclass of ...rule.metaconstruct.ProgramMetaConstruct.
 */

package de.uka.ilkd.key.java.recoderext;

import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.reference.TypeReference;

public class RKeYMetaConstructType extends TypeReference
    implements KeYRecoderExtension {


    /**
     * 
     */
    private static final long serialVersionUID = -8028793181207056503L;
    /**
     Child
     */
    protected Expression child=null;
    protected String myname="";

    protected RKeYMetaConstructType(RKeYMetaConstructType proto) {
        super(proto);
        if (proto.child != null) {
            child = proto.child.deepClone();
        }
    }

    public RKeYMetaConstructType() {
    }


    /**
     Returns the number of children of this node.
     @return an int giving the number of children of this node
    */
    public int getChildCount() {
        int result = 0;
        if (child    != null) result++;
        return result;
    }

    /**
     Returns the child at the specified index in this node's "virtual"
     child array
     @param index an index into this node's "virtual" child array
     @return the program element at the given position
     @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
                of bounds
    */
    public ProgramElement getChildAt(int index) {
        if (child != null) {
            if (index == 0) return child;
        }
        throw new ArrayIndexOutOfBoundsException();
    }


    public int getChildPositionCode(ProgramElement child0) {
        // role 0: child
        if (child0 == child) {
            return 0;
        }
        return -1;
    }

    public int getIndexOfChild(ProgramElement pe) {
	if (pe==child) {
	    return 0;
	}
	return -1;
    }

    @Deprecated
    public int getIndexOfChild(int posCode) {
	if (posCode==getChildPositionCode(child)) {
	    return 0;
	}
	return -1;
    }

    public int getRoleOfChild(int i) {
	if (i==0) return getChildPositionCode(child);
	return -1;
    }


    /**
     * sets a String myname of this meta construct like 'unwind-loop'
     * @param s the String
     */
    public void setName(String s) {
	myname=s;
    }

    public String getName0() {
	return myname;
    }

    /**
     Get child.
     @return the expression.
     */

    public Expression getChild() {
        return child;
    }

    /**
     Set child.
     @param expression a expression.
     */

    public void setChild(Expression expression) {
        child = expression;
    }

    /**
     Get the number of expression in this container.
     @return the number of expressions.
     */

    public int getExpressionCount() {
        return (child != null) ? 1 : 0;
    }

    /*
      Return the expression at the specified index in this node's
      "virtual" expression array.
      @param index an index for a expression.
      @return the expression with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */

    public Expression getExpressionAt(int index) {
        if (child != null && index == 0) {
            return child;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    //don't think we need it
    public void accept(SourceVisitor v) {
    }
    
    //???
    public TypeReference deepClone() {
	return null;
    }


}
