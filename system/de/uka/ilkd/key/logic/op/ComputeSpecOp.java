// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
/*
 * Created on 23.12.2004
 */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;

/**
 * This compute spec operator is used for computing spec. It is a
 * non-rigid operator which forces the update simplifier to
 * stop before and to <strong>not</strong> delete anything. 
 * @author bubel
 */
public class ComputeSpecOp extends Junctor implements NonRigid {

    /**
     * @param name
     * @param arity
     */
    ComputeSpecOp() {
        super(new Name("^"), 1);      
    }

    public boolean isRigid(Term t) {
        return false;
    }
    
}
