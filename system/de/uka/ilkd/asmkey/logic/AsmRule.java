// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.logic;


import de.uka.ilkd.asmkey.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.NonRigidFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;


/** Instances of theses classes represent named ASM rules (procedures).
 * Some are derived and the other are non-derived and called abstract.
 * Abstract ASM rules serves to proof PO for taclets and others.
 *
 * @author Stanislas Nanchen
 * @author Hubert Schmid
 */
public interface AsmRule extends Operator {

    public final class DerivedAsmRule extends NonRigidDerivedFunction implements AsmRule {
	
	/** creates a new named asm rule with uninitialized body. */
	public DerivedAsmRule(Name name,
			      FormalParameter[] params,
			      Term term,
			      boolean isRecursive) {
	    super(name, PrimitiveSort.ASMRULE, params, term, isRecursive);
	}
	
	public AsmProgram program() {
	    return (AsmProgram) body();
	}
    }

    public final class AbstractAsmRule extends NonRigidFunction implements AsmRule {
	
	/** create a new abstract asm rule*/
	public AbstractAsmRule(Name name) {
	    super(name, PrimitiveSort.ASMRULE, new Sort[0]);
	}

    }
    
    
}
