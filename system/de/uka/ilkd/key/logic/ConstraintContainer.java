// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

/** ConstraintContainer wraps constraints */
public class ConstraintContainer {
    private Constraint co;
    
    public ConstraintContainer() {}
    
    public Constraint val() {
	return co;
    }
    
    public void setVal(Constraint p_co) {
	co=p_co;
    }
}
