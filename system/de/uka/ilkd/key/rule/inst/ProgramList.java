// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.java.ArrayOfProgramElement;
import de.uka.ilkd.key.logic.op.SVSubstitute;

public class ProgramList implements SVSubstitute {

    private final ArrayOfProgramElement list;


    public ProgramList(ArrayOfProgramElement list) {
	assert list != null : "Constructor of ProgramList must"+
            " not be called with null argument";
        this.list = list;
    }

    public ArrayOfProgramElement getList() {
	return list;
    }
    
    public boolean equals(Object o) {
        if (!(o instanceof ProgramList)) {
            return false;
        }
        return list.equals(((ProgramList)o).list);
    }
    
    public int hashCode() {
        return list.hashCode();
    }
    
}
