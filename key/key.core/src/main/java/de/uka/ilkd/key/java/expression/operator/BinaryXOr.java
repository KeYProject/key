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

package de.uka.ilkd.key.java.expression.operator;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.visitor.Visitor;

/**
 *  Binary X or.
 *  @author <TT>AutoDoc</TT>
 */

public class BinaryXOr extends BinaryOperator {


    /**
     *      Binary X or.
     *      @param children an ExtList with all children of this node
     *      the first children in list will be the one on the left
     *      side, the second the one on the  right side.
     */

    public BinaryXOr(ExtList children) {
        super(children);
    }


    /**
 *      Get precedence.
 *      @return the int value.
     */

    public int getPrecedence() {
        return 8;
    }

    /**
 *      Get notation.
 *      @return the int value.
     */

    public int getNotation() {
        return INFIX;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnBinaryXOr(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printBinaryXOr(this);
    }
}