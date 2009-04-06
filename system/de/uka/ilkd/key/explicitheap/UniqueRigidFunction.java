// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.explicitheap;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.Sort;



public class UniqueRigidFunction extends RigidFunction {

    public UniqueRigidFunction(Name name, Sort sort, Sort[] argSorts) {
        super(name, sort, argSorts);
    }


    public UniqueRigidFunction(Name name, Sort sort, ArrayOfSort argSorts) {
        super(name, sort, argSorts);            
    }
}