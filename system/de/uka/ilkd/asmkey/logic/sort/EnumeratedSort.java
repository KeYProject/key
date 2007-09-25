// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic.sort;

import de.uka.ilkd.asmkey.unit.base.Bool;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.rule.Taclet;

public class EnumeratedSort extends PrimitiveSort {

    public static final EnumeratedSort BOOLEAN = new EnumeratedSort(Bool.builtInName(),
								    Bool.builtInConsts());

    private Function[] consts;
    private Taclet[] taclets;

    public EnumeratedSort (Name name, Name[] consts) {
	super(name);
	this.consts = createConstants(consts);
	this.taclets = createTaclets();
    }
    
    private final Function[] createConstants(Name[] consts) {
	ArrayOfSort empty = new ArrayOfSort();
	Function[] funcs = new Function[consts.length];
	for(int i=0; i<consts.length; i++) {
	    funcs[i] = new RigidFunction(consts[i], this, empty);
	}
	return funcs;
    }
    
    private final Taclet[] createTaclets() {
	return new Taclet[0];
    }

    public Function[] getConstants() {
	return consts;
    }
    
    public Taclet[] getTaclets() {
	return taclets;
    }

    public static PrimitiveSort builtInSort(Name name) {
	if (BOOLEAN.name().equals(name)) {
	    return BOOLEAN;
	} else {
	    return null;
	}
    }
}

