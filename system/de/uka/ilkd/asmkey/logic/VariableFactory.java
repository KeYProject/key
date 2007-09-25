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
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.SetOfQuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;

/** For generating unique names
 *
 * @author Stanislas Nanchen
 */

public class VariableFactory {

    private int count = 0;
    
    public VariableFactory() {
	super();
    }
    
    public LogicVariable createNewVariable(Term term, String prefix, Sort sort) {
	SetOfQuantifiableVariable set = term.freeVars();
	for (;;) {
	    LogicVariable v = new LogicVariable(new Name(prefix + (count++)), sort);
	    if (!set.contains(v)) {
		return v;
	    }
	}
    }
}
