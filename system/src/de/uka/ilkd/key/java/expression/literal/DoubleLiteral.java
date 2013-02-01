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



package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Double literal.
 *  @author <TT>AutoDoc</TT>
 */

public class DoubleLiteral extends Literal {

    /**
 *      Textual representation of the value.
     */

    protected final String value;

    /**
 *      Double literal.
     */

    public DoubleLiteral() {
        this.value="0.0";
    }

    /**
 *      Double literal.
 *      @param value a double value.
     */

    public DoubleLiteral(double value) {
        this.value="" + value;
    }

    /**
     *      Double literal.
     *      @param children list with all children(here:comments)
     *        May contain: Comments
     *      @param value a string.
     */

    public DoubleLiteral(ExtList children, String value) {
	super(children);
        this.value=value;
    }

    /**
 *      Double literal.
 *      @param value a string.
     */

    public DoubleLiteral(String value) {
        this.value=value;
    }

    /** tests if equals
     */
    public boolean equalsModRenaming(	SourceElement o, 
										NameAbstractionTable nat) {
		if (!(o instanceof DoubleLiteral)) {
		    return false;
		}
		return ((DoubleLiteral)o).getValue().equals(getValue()); 
    }
    
    public int hashCode(){
    	int result = 17;
    	result = 37 * result + getValue().hashCode();
    	return result;
    }
    
    public boolean equals(Object o){
    	return super.equals(o);
    }

    /**
 *      Get value.
 *      @return the string.
     */

    public String getValue() {
        return value;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnDoubleLiteral(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printDoubleLiteral(this);
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
	return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_DOUBLE);
    }

}
