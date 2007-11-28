// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.parser.ocl;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;

/**
 * Collects all axioms, which are created during the translation.
 * 
 */
public class AxiomCollector {

	private static final TermBuilder tb = TermBuilder.DF;
		
	private Map /*Named -> Term */ axioms = new HashMap();
	
        
	public void collectAxiom(Named n, Term a) {
		if (axioms.containsKey(n)) {
			axioms.put(n, (tb.and((Term)axioms.get(n), a)));
		} else {
			axioms.put(n, a);
		}
		
	}
	
	
	/**
	 * Returns all collected axioms.
	 * 
	 * @return Map from defined symbols to axioms
	 */
	public Map /*Named -> Term*/ getAxioms() {
	    return axioms;
	}
}
