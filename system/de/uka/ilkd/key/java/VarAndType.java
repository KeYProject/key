// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public class VarAndType {

    ProgramVariable pv;
    KeYJavaType kjt;

    public VarAndType(ProgramVariable pv, KeYJavaType kjt) {
	this.pv=pv;
	this.kjt=kjt;
    }

    public KeYJavaType getKeYJavaType() {
	return kjt;
    }

    public ProgramVariable getProgramVariable() {
	return pv;
    }
    

}
