// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;

/**
 * This class represents currently only static final fields initialised with 
 * a compile time constant. These fields cannot occur on the left side of an 
 * update.
 */
public class ProgramConstant extends ProgramVariable {

    // the value of the initializer as a literal, if this variable is
    // a compile-time constant, <code>null</code> otherwise
    private final Literal compileTimeConstant;
    
    public ProgramConstant(ProgramElementName name, 
            KeYJavaType        t, 
            KeYJavaType        containingType,
            boolean            isStatic,
            Literal            compileTimeConstant) {
        super(name, t.getSort(), t, containingType, isStatic, false, false);
        this.compileTimeConstant = compileTimeConstant;
    }
    
    /**
     * @return the value of the initializer as a literal, if this
     * variable is a compile-time constant, </code>null</code>
     * otherwise
     */
    public Literal getCompileTimeConstant () {
        return compileTimeConstant;
    }
    
    /**
     * @return true if the value of "term" having this operator as
     * top-level operator and may not be changed by modalities
     */
    public boolean isRigid(Term t) {
        return t.arity() == 0 && t.op() == this;
    }
    
    /** calls the corresponding method of a visitor in order to    
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(de.uka.ilkd.key.java.visitor.Visitor v) {
        v.performActionOnProgramConstant(this);
    }
}
