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

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;

/**
 * This class is a superclass for integer literals (Int, Long, Char).
 * It provides a getValue() method to receive the actual value of the literal as well as
 * getValueString() to get a String representation. Subclasses of this class perform range checks at
 * creation time. This means once a literal is created it is certainly valid.
 * @author Wolfram Pfeifer
 */
public abstract class AbstractIntegerLiteral extends Literal {

    /**
     * Empty default constructor.
     */
    protected AbstractIntegerLiteral() {
    }

    /**
     * Constructor for Recoder2KeY transformation.
     *
     * @param children the children of this AST element as KeY classes, may contain: Comments
     */
    protected AbstractIntegerLiteral(ExtList children) {
        super(children);
    }

    /**
     *
     * @return the actual value of the literal as a long
     */
    public abstract long getValue();

    /**
     *
     * @return the actual value of the literal converted to a decimal String. If the literal
     *         represents a negative value, the first character is a '-' sign.
     */
    public abstract String getValueString();

    @Override
    public boolean equals(Object o) {
        return super.equals(o);
    }

    @Override
    public boolean equalsModRenaming(SourceElement o, NameAbstractionTable nat) {
        if (!(o.getClass() == this.getClass())) {
            return false;
        }
        return ((AbstractIntegerLiteral)o).getValue() == getValue();
    }

    @Override
    public String toString() {
        return getValueString();
    }

    @Override
    protected int computeHashCode() {
        int localHash = (int) (17 * super.computeHashCode() + getValue());
        return localHash;
    }

    @Override
    public Name getLDTName() {
        return IntegerLDT.NAME;
    }

    /**
     * Checks if the prefix of the given String indicates a decimal literal.
     * This method does <b>not</b> check if the literal is actually valid, it just checks the
     * prefix indicating the base of the literal. The base prefix is found even if the String
     * contains a preceding sign ('+' or '-').
     * @param literalStr the given String to check
     * @return true iff the String represents a decimal literal, which means it does neither have
     * a hexadecimal ("0x"), binary ("0b"), nor octal ("0") prefix. Note that the literal "0" is
     * decimal too.
     */
    public static boolean representsDecLiteral(String literalStr) {
        if (literalStr.length() == 0) {
            throw new NumberFormatException(literalStr + "does not represent a number.");
        }

        if (literalStr.charAt(0) == '-' || literalStr.charAt(0) == '+') {
            literalStr = literalStr.substring(1);
        }

        /* we have to remove the char indicating a long literal as the length of the literal is
         * used later on when checking for an octal prefix */
        if (literalStr.endsWith("l") || literalStr.endsWith("L")) {
            literalStr = literalStr.substring(0, literalStr.length() - 1);
        }

        int radix = 10;
        if (literalStr.startsWith("0x") || literalStr.startsWith("0X")) {        // hex
            radix = 16;
            //literalStr = literalStr.substring(2);     // cut of '0x'
        } else if (literalStr.startsWith("0b") || literalStr.startsWith("0B")) { // bin
            radix = 2;
            //literalStr = literalStr.substring(2);     // cut of '0b'
        } else if (literalStr.startsWith("0") && literalStr.length() > 1) {      // oct
            radix = 8;
            //literalStr = literalStr.substring(1);     // cut of leading '0'
        }
        return radix == 10;
    }
}
