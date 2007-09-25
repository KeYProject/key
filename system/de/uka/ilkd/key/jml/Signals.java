// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.jml;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * Provides an encapsulation for a single signals clause.
 */
public class Signals{

    private final KeYJavaType kjt;
    private final ProgramVariable v;
    private final Term cond;

    public Signals(KeYJavaType kjt, ProgramVariable v, Term cond){
	this.kjt = kjt;
	this.v = v;
	this.cond = cond;
    }

    public KeYJavaType type(){
	return kjt;
    }

    public ProgramVariable variable(){
	return v;
    }

    public Term condition(){
	return cond;
    }
}
