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

import de.uka.ilkd.asmkey.logic.dfinfo.DFException;
import de.uka.ilkd.asmkey.logic.dfinfo.DFInfo;
import de.uka.ilkd.asmkey.logic.dfinfo.DFInfoFactory;
import de.uka.ilkd.asmkey.parser.env.DefaultEnvironment;
import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.ListOfNamed;

/** This class performs:
 * - determination of : update info.
 *
 * @author Stanislas Nanchen
 */

class UpdateDFInfo {

    private HashMapFromAsmRuleToAsmProgram procs;
    private DefaultEnvironment env;
    private boolean fixPointFlag;
    private DFInfoFactory factory;

    public UpdateDFInfo(DefaultEnvironment env, HashMapFromAsmRuleToAsmProgram procs) {
	this.env = env;
	this.procs = procs;
	factory = new DFInfoFactory(env);
    }

    public void doAnalysis() throws DFException {
	ListOfNamed namedRules = env.getRules();
	AsmRule namedRule;
	
	IteratorOfNamed it; 

	fixPointFlag = false;
	while(!fixPointFlag) {
	    fixPointFlag = true;
	    it = namedRules.iterator();
	    while (it.hasNext()) {
		namedRule = (AsmRule) it.next();
		computeInfo(procs.get(namedRule));
	    }
	}
    }

    DFInfo computeInfo(AsmProgram rule) throws DFException {
	AsmProgram sub;
	DFInfo result = rule.getUpdateDFInfo();
	DFInfo temp;

	if (rule.op() instanceof AsmRule) {
	    temp = computeInfo(procs.get((AsmRule)rule.op()));
	    if (temp != result) {
		result = setUpdateDFInfo(rule, temp);
	    }
	} else if (rule.op() == AsmProgramOperator.SKIP) {
	    // for skip, we have the empty set.
	    if (!result.isEqual(factory.getEmptyDFInfo())) {
		result = setUpdateDFInfo(rule, factory.getEmptyDFInfo());
	    }
	} else if (rule.op() == AsmProgramOperator.ASSIGN) {
	    temp = factory.getDFInfo(rule.sub(0).op().name());
	    if (!result.isEqual(temp)) {
		result = setUpdateDFInfo(rule, temp);
	    }
	} else {
	    temp = factory.getEmptyDFInfo();
	    for(int i = 0; i<rule.arity(); i++) {
		if (rule.sub(i) instanceof AsmProgram) {
		    sub = (AsmProgram) rule.sub(i);
		    temp = temp.union(computeInfo(sub));
		}
	    }
	    if (!result.isEqual(temp)) {
		result = setUpdateDFInfo(rule, temp);
	    }
	}
	return result;
    }

    DFInfo setUpdateDFInfo(AsmProgram rule, DFInfo info) {
	rule.setUpdateDFInfo(info);
	fixPointFlag = false;
	return info;
    }
    
}
