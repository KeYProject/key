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

import java.math.BigInteger;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.visitor.Visitor;

/**
 *  Char literal.
 *  @author <TT>AutoDoc</TT>
 */
public class CharLiteral extends AbstractIntegerLiteral {

    /**
     * A decimal String representation of the 16 bit char value represented by this CharLiteral.
     */
    private final String valueStr;

    /**
     * The actual char this CharLiteral represents.
     */
    private final char charVal;

    /**
     * Creates a new CharLiteral from the given char.
     * @param charVal a char value.
     */
    public CharLiteral(char charVal) {
        //this.valueStr = "'" + charVal + "'";
        this.charVal = charVal;
        this.valueStr = "" + (int)charVal;
    }

    /**
     * Creates a new CharLiteral from the given String. The String must be of the form
     * <code>'c'</code> (with c being an arbitrary char).
     * @param children an ExtList with all children(comments). May contain: Comments
     * @param valueStr a string.
     */
    public CharLiteral(ExtList children, String valueStr) {
        super(children, false);
//        this.valueStr = valueStr;
//        this.charVal = valueStr.charAt(1);
        this.charVal = valueStr.charAt(1);
        this.valueStr = "" + (int)charVal;
    }

    /**
     * Creates a new CharLiteral from the given String. The String must be of the form
     * <code>'c'</code> (with c being an arbitrary char).
     * @param valueStr a string.
     */
    public CharLiteral(String valueStr) {
//        this.valueStr=valueStr;
//        this.charVal=valueStr.charAt(1);
        this.charVal = valueStr.charAt(1);
        this.valueStr = "" + (int)charVal;
    }

//    /** tests if equals
//     */
//    public boolean equalsModRenaming(SourceElement o,
//            NameAbstractionTable nat) {
//        if (!(o instanceof CharLiteral)) {
//            return false;
//        }
//        return ((CharLiteral)o).getValue().equals(getValue());
//    }
//
//    public int hashCode(){
//      int result = 17;
//      result = 37 * result + getValue().hashCode();
//      return result;
//    }
//
//    public boolean equals(Object o){
//      return super.equals(o);
//    }

    /**
     * Returns the decimal value of the char.
     * @return the decimal value of the char as a BigInteger
     */
    public BigInteger getValue() {
        return BigInteger.valueOf(charVal);
    }

//    public char getCharValue() {
//        return charVal;
//    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnCharLiteral(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printCharLiteral(this);
    }

    @Override
    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_CHAR);
    }

    @Override
    public String toString() {
        return "'" + charVal + "'";
    }

    @Override
    public String getValueString() {
        return valueStr;
    }
}
