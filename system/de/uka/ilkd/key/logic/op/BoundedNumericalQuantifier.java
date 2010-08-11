// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

public class BoundedNumericalQuantifier extends Op {
     
    BoundedNumericalQuantifier(Name name) {
        super(name);
    }
    
    public int arity() {
        return 3;
    }

    public Sort sort(Term[] term) {
        return term[2].sort();
    }

    public boolean validTopLevel(Term term) {
        return term.arity()==arity();
    }

    public Sort argSort(int i) {
	return Sort.ANY;
    }

}
