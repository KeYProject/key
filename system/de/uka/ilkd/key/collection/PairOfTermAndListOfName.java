// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.collection;

import de.uka.ilkd.key.logic.ListOfName;
import de.uka.ilkd.key.logic.Term;

/**
 * Wraps a Term and a ListOfName in one object to allow returning them by one
 * function call.
 */
public class PairOfTermAndListOfName {

    private Object[] pair = new Object[2];

    public PairOfTermAndListOfName(Term t, ListOfName l) {
        pair[0] = t;
        pair[1] = l;
    }

    public Term getTerm() {
        return (Term) pair[0];
    }

    public ListOfName getListOfName() {
        return (ListOfName) pair[1];
    }

}
