// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This class represents all kind of local and instance variables. In addition it represents
 * static variables, which are no compile time constants, i.e. which are not final or
 * not initialised with a compile time constant.
 * 
 */
public class LocationVariable extends ProgramVariable implements Location {

    public LocationVariable(ProgramElementName name, 
            KeYJavaType        t, 
            KeYJavaType        containingType,
            boolean            isStatic,
            boolean            isModel,
            boolean            isGhost) {
        super(name, t.getSort(), t, containingType, 
                isStatic, isModel, isGhost);
    }

    public LocationVariable(ProgramElementName name, 
            KeYJavaType        t, 
            KeYJavaType        containingType,
            boolean            isStatic) {
        super(name, t.getSort(), t, containingType, isStatic, false, false);
    }

    public LocationVariable(ProgramElementName name, KeYJavaType t) {
        super(name, t.getSort(), t, null, false, false, false);
    }
    
    public LocationVariable(ProgramElementName name, KeYJavaType t, boolean isFinal) {
        super(name, t.getSort(), t, null, false, false, false, isFinal);
    }

    public LocationVariable(ProgramElementName name, Sort s) {
        super(name, s, null, null, false, false, false);
    }
    
    /**
     * @return true if the value of "term" having this operator as
     * top-level operator and may not be changed by modalities
     */
    public boolean isRigid (Term term) {
        return false;
    }
    
    /** calls the corresponding method of a visitor in order to    
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(de.uka.ilkd.key.java.visitor.Visitor v) {
        v.performActionOnLocationVariable(this);
    }

}
