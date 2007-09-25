// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * @see DerivedFunction
 */
public class RigidDerivedFunction extends DerivedFunction {

    public RigidDerivedFunction(Name name, Sort sort, FormalParameter[] args, Term body,
				boolean isRecursive) {
	super(name, sort, args, body, isRecursive);
    }

    public RigidDerivedFunction(Name name, Sort sort, FormalParameter[] args,
				boolean isRecursive) {
	this(name, sort, args, null, isRecursive);
    }

}
