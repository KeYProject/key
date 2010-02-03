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
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Wraps a SVInstantiations and a ListOfName in one object to allow returning
 * them by one function call.
 */
public class PairOfSVInstantiationsAndListOfName {

    private Object[] pair = new Object[2];

    public PairOfSVInstantiationsAndListOfName(SVInstantiations s, ListOfName l) {
        pair[0] = s;
        pair[1] = l;
    }

    public SVInstantiations getSVInstantiations() {
        return (SVInstantiations) pair[0];
    }

    public ListOfName getListOfName() {
        return (ListOfName) pair[1];
    }

}
