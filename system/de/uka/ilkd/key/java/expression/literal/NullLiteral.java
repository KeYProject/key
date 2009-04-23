// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;

/**
 *  Null literal.
 *  Is used as singleton. 
 */

public class NullLiteral extends Literal {

    public static final NullLiteral NULL=new NullLiteral(); 

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     */
    private NullLiteral() {
	super();
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnNullLiteral(this);
    }

    
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printNullLiteral(this);
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
	return javaServ.getJavaInfo().getNullType();
    }

}
