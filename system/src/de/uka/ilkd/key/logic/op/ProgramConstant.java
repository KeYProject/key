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

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.logic.ProgramElementName;

/**
 * This class represents currently only static final fields initialised with 
 * a compile time constant. These fields cannot occur on the left side of an 
 * update.
 */
public final class ProgramConstant extends ProgramVariable {

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


    @Override
    public void visit(de.uka.ilkd.key.java.visitor.Visitor v) {
        v.performActionOnProgramConstant(this);
    }
}