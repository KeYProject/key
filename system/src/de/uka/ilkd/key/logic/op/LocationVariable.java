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
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This class represents proper program variables, which are not program
 * constants. See the description of the superclass ProgramVariable for
 * more information.
 */
public final class LocationVariable extends ProgramVariable
			            implements UpdateableOperator {


    public LocationVariable(ProgramElementName name,
                        KeYJavaType        t,
                        KeYJavaType        containingType,
                        boolean            isStatic,
                        boolean            isModel,
                        boolean isGhost,
                        boolean isFinal) {
        super(name, t.getSort(), t, containingType, isStatic, isModel, isGhost, isFinal);
    }
    
    public LocationVariable(ProgramElementName name,
            		    KeYJavaType        t,
            		    KeYJavaType        containingType,
            		    boolean            isStatic,
            		    boolean            isModel) {
        super(name, t.getSort(), t, containingType, isStatic, isModel, false);
    }


    public LocationVariable(ProgramElementName name, KeYJavaType t) {
        super(name, t.getSort(), t, null, false, false, false);
    }


    public LocationVariable(ProgramElementName name, KeYJavaType t, boolean isFinal) {
        super(name, t.getSort(), t, null, false, false, false, isFinal);
    }

    public LocationVariable(ProgramElementName name, KeYJavaType t, boolean isGhost, boolean isFinal) {
        super(name, t.getSort(), t, null, false, false, isGhost, isFinal);
    }



    public LocationVariable(ProgramElementName name, Sort s) {
        super(name, s, null, null, false, false, false);
    }


    @Override
    public void visit(de.uka.ilkd.key.java.visitor.Visitor v) {
        v.performActionOnLocationVariable(this);
    }
}