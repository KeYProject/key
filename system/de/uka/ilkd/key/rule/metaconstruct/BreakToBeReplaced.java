// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.statement.Break;
import de.uka.ilkd.key.logic.op.ProgramVariable;

class BreakToBeReplaced {

    private Break brk;
    private ProgramVariable pvar;

    public BreakToBeReplaced(Break brk, 
			     ProgramVariable pvar) {
	this.brk  = brk;
	this.pvar = pvar;
    }

    public BreakToBeReplaced(Break brk) {
	this.brk  = brk;
	this.pvar = null;
    }

    Break getBreak() {
	return brk;
    }

    ProgramVariable getProgramVariable() {
	return pvar;
    }
    
    void setProgramVariable(ProgramVariable pvar) {
	this.pvar = pvar;
    }

}
