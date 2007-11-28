// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.logic.ldt;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.Function;


public class IntegerLDT extends AbstractIntegerLDT {
      
    public IntegerLDT(Namespace sorts, Namespace functions) {
        super(new Name("int"), sorts, functions, null);
    }
    

    public Function getInBoundsPredicate() {
	return null;
    }
}
