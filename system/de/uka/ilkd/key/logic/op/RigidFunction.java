// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.Sort;


public class RigidFunction extends Function {
    
    private final boolean unique;

    public RigidFunction(Name name, Sort sort, Sort[] argSorts) {
	super(name, sort, argSorts);
	unique = false;
    }


    public RigidFunction(Name name, Sort sort, ArrayOfSort argSorts) {
	super(name, sort, argSorts);
	unique = false;
    }


    public RigidFunction(Name name, Sort sort, Sort[] argSorts, boolean unique) {
	super(name, sort, argSorts);
	this.unique = unique;
    }


    public RigidFunction(Name name, Sort sort, ArrayOfSort argSorts, boolean unique) {
	super(name, sort, argSorts);
	this.unique = unique;
    }
    
    public boolean isUnique() {
	return unique;
    }
    
    @Override
    public boolean isRigid() {
	return true;
    }    
}
