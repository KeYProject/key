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

/** This class computes the strongly connected components
 * using the tarjan algorithm (depth-first). 
 */


class SCC {

    private HashMapFromAsmRuleToAsmProgram procs;
    private HashMapFromAsmProgramToInteger visitedToken;
    private HashMapFromAsmProgramToInteger lowLink;
    private ListOfAsmProgram stack;
    private DefaultEnvironment env;
    private HashMapFromAsmProgramToListOfAsmProgram sccs;
    private int c;

    public SCC (DefaultEnvironment env, HashMapFromAsmRuleToAsmProgram procs) {
	visitedToken = new HashMapFromAsmProgramToInteger();
	lowLink = new HashMapFromAsmProgramToInteger();
	stack = SLListOfAsmProgram.EMPTY_LIST;
	sccs = new HashMapFromAsmProgramToListOfAsmProgram();
	this.procs = procs;
	//sccs = SLListOfListOfAsmProgram.EMPTY_LIST;
	this.env = env;
	c = 0;
    }
    
    public void doAnalysis() {
	ListOfNamed namedRules = env.getRules();
	
	IteratorOfNamed it = namedRules.iterator();
	AsmRule namedRule;

	while (it.hasNext()) {
	    namedRule = (AsmRule) it.next();
	    if (! visitedToken.containsKey(procs.get(namedRule))) {
		c = 0;
		sc(procs.get(namedRule));
	    }
	}
	it = namedRules.iterator();
	while (it.hasNext()) {
	    namedRule = (AsmRule) it.next();
	    if(sccs.get(procs.get(namedRule)).size() > 1) {
		//namedRule.setRecursiveFlag(true);
	    }
	}
    }

    private void sc(AsmProgram v) {
	AsmProgram w;
	Integer integer = new Integer(c);
	
	c++;
	
	visitedToken.put(v, integer);
	lowLink.put(v, integer);
	stack = stack.prepend(v);
	
	if (v.op() instanceof AsmRule) {
	    visit(v, procs.get((AsmRule) v.op()));
	} else {
	    for(int i = 0; i<v.arity(); i++) {
		if (v.sub(i) instanceof AsmProgram) {
		    visit(v, (AsmProgram) v.sub(i));
		}
	    }
	}

	if(lowLink.get(v).compareTo(visitedToken.get(v)) == 0) {
	    // we have a scc component. !
	    ListOfAsmProgram component = SLListOfAsmProgram.EMPTY_LIST;
	    w = null;
	    while (v != w) {
		w = stack.head();
		stack = stack.tail();
		component = component.prepend(w);
	    }
	    IteratorOfAsmProgram it = component.iterator();
	    while(it.hasNext()) {
		sccs.put(it.next(), component);
	    }
	}
    }

    private void visit(AsmProgram v, AsmProgram w) {
	Integer vint, wint;

	if (visitedToken.containsKey(w)) {
	    if (! sccs.containsKey(w)) {
		vint = lowLink.get(v);
		wint = visitedToken.get(w);

	    
		lowLink.put(v, min(vint, wint));
	    }
	} else {
	    sc(w);
	    
	    vint = lowLink.get(v);
	    wint = lowLink.get(w);
	    lowLink.put(v, min(vint, wint));
	}
    }


    private static Integer min(Integer x, Integer y) {
	if (x.compareTo(y) < 0) {
	    return x;
	} else {
	    return y;
	}
    }
    
    IteratorOfListOfAsmProgram getSSCs() {
	return sccs.values();
    }

}
