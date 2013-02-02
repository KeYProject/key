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



package de.uka.ilkd.key.java.declaration;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Implements.
 *  
 */

public class Implements extends InheritanceSpecification {

    /**
 *      Implements.
     */

    public Implements() {}

    /**
 *      Implements.
 *      @param supertype a type reference.
     */

    public Implements(TypeReference supertype) {
        super(supertype);
    }

    /**
     *      Implements.
     *      @param typeRefs a type reference array.
     */

    public Implements(TypeReference[] typeRefs) {
        super(typeRefs);
    }

    /**
     *      Implements.
     *      @param children  containing the children. May include: 
     *            a Comment,
     * 	          several TypeReference (as references to the supertypes)
     * 
     */
    public Implements(ExtList children) {
        super(children);
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnImplements(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printImplements(this);
    }
}
