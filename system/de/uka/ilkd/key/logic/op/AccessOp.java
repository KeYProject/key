// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramInLogic;
import de.uka.ilkd.key.logic.Term;

public abstract class AccessOp extends Op 
    implements Operator, ProgramInLogic, Location, NonRigid {

    /**
     *creates an AccessOp
     */
    AccessOp(Name name){
        super(name);
    }

    /**
     * @return true if the value of "term" having this operator as
     * top-level operator and may not be changed by modalities
     */
    public boolean isRigid (Term term) {
	return false;
    }

    /**
     * @return true if the operator is a shadowed 
     */
    public abstract boolean isShadowed();

    
}
