// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
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
 *  Boolean literal.
 *  @author <TT>AutoDoc</TT>
 */
public class BooleanLiteral extends Literal {

    public final static BooleanLiteral TRUE = new BooleanLiteral(true);
    public final static BooleanLiteral FALSE = new BooleanLiteral(false);


    protected final boolean value;

    
    /**
     * get boolean literal for the given <code>value</code>. This supports
     * use of single literals, but we do not force it. 
     * @param val a boolean specifying the literal to be returned
     * @return the BooleanLiteral representing <tt>val</tt>
     */
    public static BooleanLiteral getBooleanLiteral(boolean val) {
        return val ? TRUE : FALSE; 
    }

    /**
 *      Boolean literal.
 *      @param value a boolean value.
     */

    private BooleanLiteral(boolean value) {
        this.value=value;
    }

    /**
     *      Boolean literal.
     *      @param children list with all children
     *       May contain: Comments
     *      @param value a boolean value.
     */
    public BooleanLiteral(ExtList children, boolean value) {
	super(children);
        this.value=value;
    }

    /**
 *      Get value.
 *      @return the string.
     */

    public boolean getValue() {
        return value;
    }

    /**
 *      Get value.
 *      @return the string.
     */

    public String getName() {
        return (value ? "true" : "false") ;
    }

    /** tests if equals
     */
    public boolean equalsModRenaming(	SourceElement o, 
                                     	NameAbstractionTable nat) {
        if (!(o instanceof BooleanLiteral)) {
            return false;
        }
        return ((BooleanLiteral)o).getValue() == getValue(); 
    }
    
    public int hashCode(){
    	int result = 17;
    	result = 37 * result + (getValue() ? 0 : 1);
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
	v.performActionOnBooleanLiteral(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printBooleanLiteral(this);
    }


    public KeYJavaType getKeYJavaType(Services javaServ) {
	return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_BOOLEAN);
    }

}
