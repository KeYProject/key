// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.logic;

import de.uka.ilkd.asmkey.logic.dfinfo.DFInfo;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;

/** Special implementation of
 * rules, with support for static analysis of rules
 * in particular, simplification of con and joinable
 * predicates.
 *
 * @author Stanislas Nanchen
 */

class AsmProgram extends AsmTerm implements UpdateDFInfoContainer, AccessDFInfoContainer {
   
    private DFInfo may_update_functions = null;
    private DFInfo mayAccessFunctions = null;


    public DFInfo getAccessDFInfo() {
	return mayAccessFunctions;
    }

    public void setAccessDFInfo(DFInfo info) {
	mayAccessFunctions = info;
    }

    public DFInfo getUpdateDFInfo() {
	return may_update_functions;
    }

    public void setUpdateDFInfo(DFInfo info) {
	may_update_functions = info;
    }


    AsmProgram(AsmOperator op, Term[] terms, ArrayOfQuantifiableVariable vars) {
	super(op,terms,vars);
    }

    public Term sub(int index) {
	Term term = super.sub(index);
	if (op() == AsmProgramOperator.FORALL) {
	    // ADD the variable.. somehow...
	} 
	return term;
    }

}

