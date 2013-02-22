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
 *  Float literal.
 *  @author <TT>AutoDoc</TT>
 */

public class FloatLiteral extends Literal {

    /**
 *      Textual representation of the value.
     */

    protected final String value;

    /**
 *      Float literal.
 *      @param value a float value.
     */

    public FloatLiteral(float value) {
        this.value="" + value + 'F';
    }

    /**
     *      Float literal.
     *      @param children an ExtList with all children(here:comments)
     *      @param value a string.
     */

    public FloatLiteral(ExtList children,String value) {
	super(children);
        this.value=(value.endsWith("F") || value.endsWith("f")) ? value :
              (value + 'F');
    }

    /**
     *      Float literal.
     *      @param value a string.
     */

    public FloatLiteral(String value) {
        this.value=(value.endsWith("F") || value.endsWith("f")) ? value :
              (value + 'F');
    }

    /** tests if equals
     */
    public boolean equalsModRenaming(	SourceElement o, 
										NameAbstractionTable nat){
		if (!(o instanceof FloatLiteral)) {
		    return false;
		}
		return ((FloatLiteral)o).getValue().equals(getValue()); 
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
	v.performActionOnFloatLiteral(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printFloatLiteral(this);
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
	return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_FLOAT);
    }

}
