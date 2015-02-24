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

package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;
/**
 *  Extends.
 *  @author <TT>AutoDoc</TT>
 */

public class Extends extends InheritanceSpecification {

    /**
     *      Extends.
     *      @param supertype a type reference.
     */
    public Extends(TypeReference supertype) {
        super(supertype);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes. May
     * include: 
     * 	several TypeReference (as references to the supertypes)
     * 	a Comment
     */     
    public Extends(ExtList children) {
	super(children);
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnExtends(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printExtends(this);
    }
}