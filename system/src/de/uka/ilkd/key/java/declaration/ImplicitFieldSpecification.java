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

import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/* An implicit field specification. In KeY we store information about states of 
 * classes and/or objects as static or instance fields
 *  (e.g. if a class is initialized or an object created). To avoid name clashes
 *  the name of implicit fields is enclosed by angle brackets.  
 */
public class ImplicitFieldSpecification extends FieldSpecification {

    /**
     * Implicit Field specification.
     */
    public ImplicitFieldSpecification() {}

    /**
     * Implicit Field specification.
     * @param var the ProgramVariable representing this concrete field
     */
    public ImplicitFieldSpecification(ProgramVariable var) {
        this(var, var.getKeYJavaType());
    }

    /**
     *      Implicit Field specification.
     *      @param var the ProgramVariable representing this concrete field
     *      @param type the Type of this field      
     */

    public ImplicitFieldSpecification(ProgramVariable var, Type type) {
        super(var, type);
    }


    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnImplicitFieldSpecification(this);
    }


}
