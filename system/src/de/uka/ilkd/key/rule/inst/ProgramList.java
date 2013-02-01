// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.op.SVSubstitute;

public class ProgramList implements SVSubstitute {

    private final ImmutableArray<ProgramElement> list;


    public ProgramList(ImmutableArray<ProgramElement> list) {
	assert list != null : "Constructor of ProgramList must"+
            " not be called with null argument";
        this.list = list;
    }

    public ImmutableArray<ProgramElement> getList() {
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
