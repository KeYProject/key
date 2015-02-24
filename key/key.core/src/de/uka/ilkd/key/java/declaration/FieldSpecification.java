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

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.util.ExtList;

/* FieldSpecification
 * taken from COMPOST and changed to achieve an immutable structure
 */

public class FieldSpecification extends VariableSpecification
        implements Field {

    /**
     *      Field specification.
     */

    public FieldSpecification() {}

    public FieldSpecification(ProgramVariable var) {
        this(var, var.getKeYJavaType());
    }

    /**
     *      Field specification.
     *      @param var the ProgramVariable representing this concrete field
     *      @param type the Type of this field      
     */

    public FieldSpecification(ProgramVariable var, Type type) {
        super(var, type);
    }

    /**
     *      Field specification.
     *      @param var the ProgramVariable representing this concrete field
     *      @param init the Expression the field is initialised with.
     *      @param type the Type of this field      
     */

    public FieldSpecification(ProgramVariable var, Expression init, Type type) {
        super(var, init, type);
    }

    /**
     *      Field specification.
     *      @param var the ProgramVariable representing this concrete field
     *      @param dimensions an int defining the dimension
     *      @param init the Expression the field is initialised with.
     *      @param type the Type of this field      
     */
    public FieldSpecification(ProgramVariable var, int dimensions, 
			      Expression init, Type type) {
        super(var, dimensions, init, type, null);
    }


    /**
     *      Field specification.
     *      @param children an ExtList with the children.
     * 	        May contain:
     * 		an Expression (as initializer of the variable)
     * 		a ProgramElementName (as name of the variable)
     * 		a Comment
     *      @param var the ProgramVariable representing this concrete field
     *      @param dimensions an int defining the dimension
     *      @param type the Type of this field      
     */

    public FieldSpecification(ExtList children, ProgramVariable var, 
			      int dimensions, Type type) {
        super(children, var, dimensions, type);
    }

    /**
     * returns the name of the field as used in programs. In the logic
     * each field has a unique name which is composed by the class name where 
     * it is declared and its source code name 
     *
     * @return returns the name of the field as used in programs
     */
    public String getProgramName(){        
        return getProgramElementName().getProgramName(); 
    }
        
    /**
     * Test whether the declaration is static.
     */
    public boolean isStatic() {
        return ((ProgramVariable)var).isStatic();
    }

    /**
     * Test whether the declaration is private.
     */
    public boolean isPrivate() {
        return false;
    }

    /**
     * Test whether the declaration is protected.TO BE IMPLEMENTED 
     */

    public boolean isProtected() {
        return false;
    }

    /**
     * Test whether the declaration is public.TO BE IMPLEMENTED 
     */

    public boolean isPublic() {
        return false;
    }


    /**
     * Test whether the declaration is transient.TO BE IMPLEMENTED 
     */

    public boolean isTransient() {
        return false;
    }

    /**
     * Test whether the declaration is volatile.TO BE IMPLEMENTED 
     */

    public boolean isVolatile() {
        return false;
    }
    
    /**
     * Test whether the declaration is strictFp.TO BE IMPLEMENTED 
     */
    public boolean isStrictFp() {
        return false;
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnFieldSpecification(this);
    }
}