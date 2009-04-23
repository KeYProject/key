// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.logic.Term;

/**
 * Term feature for checking whether the top operator of a term has an instance
 * of a certain class
 */
public class OperatorClassTF extends BinaryTermFeature {

    private final Class opClass;

    private OperatorClassTF(Class op) {
        this.opClass = op;
    }

    public static TermFeature create(Class op) {
        return new OperatorClassTF ( op );
    }

    protected boolean filter(Term term) {
        return opClass.isInstance ( term.op () );
    }
}
