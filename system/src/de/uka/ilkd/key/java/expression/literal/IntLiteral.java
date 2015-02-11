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

package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Int literal.
 *  @author <TT>AutoDoc</TT>
 */

public class IntLiteral extends Literal {

    /**
     *      Textual representation of the value.
     */
    protected String value;

    /**
     *      Int literal.
     */
    public IntLiteral() {
        this.value = "0".intern();
    }

    /**
     *      Int literal.
     *      @param value an int value.
     */
    public IntLiteral(int value) {
        this.value=("" + value).intern();
    }

    /**
     *      Int literal.
     *      @param value a string.
     */
    public IntLiteral(String value) {
        this.value=value.intern();
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     *     May contain: Comments
     */
    public IntLiteral(ExtList children) {
	super(children);
	this.value=children.get(String.class);
    }
    
    /**
	 * Constructor for Recoder2KeY transformation.
	 * 
	 * @param children
	 *            the children of this AST element as KeY classes, may contain:
	 *            Comments
	 * @param value
	 *            the value of the literal
	 */
	public IntLiteral(ExtList children, String value) {
		super(children);
    	this.value = value.intern();
    }

    /**
     *      Get value.
     *      @return the string.
     */
    public String getValue() {
        return value;
    }


    /** tests if equals
     */
    public boolean equalsModRenaming
	( SourceElement o, NameAbstractionTable nat) {
	if (!(o instanceof IntLiteral)) {
	    return false;
	}
	return ((IntLiteral)o).getValue().equals(getValue()); 
    }
    
    public int hashCode(){
    	int result = 17;
    	result = 37 * result + getValue().hashCode();
    	return result;
    }
    
    public boolean equals(Object o){
    	return super.equals(o);
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnIntLiteral(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printIntLiteral(this);
    }


    public KeYJavaType getKeYJavaType(Services javaServ) {
	return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT);
    }

    @Override
    public Name getLDTName() {
        return IntegerLDT.NAME;
    }

}
