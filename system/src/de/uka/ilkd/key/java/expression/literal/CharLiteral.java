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
 *  Char literal.
 *  @author <TT>AutoDoc</TT>
 */

public class CharLiteral extends Literal {

    protected final String value;
    private char charVal;

    /**
 *      Char literal.
 *      @param value a char value.
     */

    public CharLiteral(char value) {
	this.value="'" + value + "'";
	this.charVal=value;
    }

    /**
     *      Char literal.
     *      @param children an ExtList with all children(comments)
     *        May contain: Comments
     *      @param value a string.
     */

    public CharLiteral(ExtList children, String value) {
	super(children);
        this.value=value;
	this.charVal=value.charAt(1);
    }

    /**
 *      Char literal.
 *      @param value a string.
     */

    public CharLiteral(String value) {
        this.value=value;
	this.charVal=value.charAt(1);
    }

    /** tests if equals
     */
    public boolean equalsModRenaming(SourceElement o, 
            NameAbstractionTable nat) {
        if (!(o instanceof CharLiteral)) {
            return false;
        }
        return ((CharLiteral)o).getValue().equals(getValue()); 
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

    public char getCharValue() {
        return charVal;
    }


    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnCharLiteral(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printCharLiteral(this);
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
	return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_CHAR);
    }

    @Override
    public Name getLDTName() {
        return IntegerLDT.NAME;
    }

}
