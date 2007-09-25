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

import de.uka.ilkd.asmkey.parser.env.DefaultEnvironment;
import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.ListOfNamed;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.util.Debug;

/** This class is the entry point for the static analysis of
 * the asms: it performs:
 * - determination of : recursive rules, hierarchical rules
 * - determination of : update and access info.
 *
 * @author Stanislas Nanchen
 */

public class StaticAnalysis {

    private DefaultEnvironment env;
    private HashMapFromAsmRuleToAsmProgram procs;

    public StaticAnalysis(DefaultEnvironment env) {
	this.env = env;
	procs = new HashMapFromAsmRuleToAsmProgram();
	prepareProcs();
    }

    private void prepareProcs() {
	ListOfNamed namedRules = env.getRules();
	IteratorOfNamed it = namedRules.iterator();
	AsmRule.DerivedAsmRule namedRule;
	AsmRule rule;
	AsmProgram proc;

	while(it.hasNext()) {
	    rule = (AsmRule) it.next();
	    if (rule instanceof AsmRule.DerivedAsmRule) {
		namedRule = (AsmRule.DerivedAsmRule) rule;
		proc = (AsmProgram) AsmProgramOperator.PROC.createTerm
		    (null, new Term[] { namedRule.body() });
		procs.put(namedRule, proc);
	    }
	}
    }

    public void analyseEnv() {

	try {
	    SCC recAnalysis = new SCC(env, procs);
	    recAnalysis.doAnalysis();
	    
	    UpdateDFInfo updAnalysis = new UpdateDFInfo(env, procs);
	    updAnalysis.doAnalysis();
	} catch (Exception e) {
	    // rethraw as parser mistake.
	    Debug.out("Exception thrown by class StaticAnalysis at doAnalysis()");
	}
    }

    public void analyse(Term term) {}
}
