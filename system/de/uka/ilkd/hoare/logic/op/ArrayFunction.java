package de.uka.ilkd.hoare.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.NonRigidFunctionLocation;
import de.uka.ilkd.key.logic.sort.Sort;

public class ArrayFunction extends NonRigidFunctionLocation {

    public ArrayFunction(Name name, Sort sort, Sort[] argSorts) {
        super(name, sort, argSorts);
        
    }

}
