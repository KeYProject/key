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



package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Binary not.
 *  @author <TT>AutoDoc</TT>
 */

public class BinaryNot extends Operator {

    /**
     *      Binary not.
     *      @param children list withh all children
     */

    public BinaryNot(ExtList children) {
        super(children);
    }


    /**
     *      Get arity.
     *      @return the int value.
     */

    public int getArity() {
        return 1;
    }

    /**
     *      Get precedence.
     *      @return the int value.
     */

    public int getPrecedence() {
        return 1;
    }

    /**
     *      Get notation.
     *      @return the int value.
     */

    public int getNotation() {
        return PREFIX;
    }

    /**
 *        Checks if this operator is left or right associative. Ordinary
 *        unary operators are right associative.
 *        @return <CODE>true</CODE>, if the operator is left associative,
 *        <CODE>false</CODE> otherwise.
     */

    public boolean isLeftAssociative() {
        return false;
    }


    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnBinaryNot(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printBinaryNot(this);
    }

    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
	final TypeConverter tc=javaServ.getTypeConverter();
	return tc.getPromotedType
	    (tc.getKeYJavaType((Expression)getChildAt(0), ec));
    
    }
}
