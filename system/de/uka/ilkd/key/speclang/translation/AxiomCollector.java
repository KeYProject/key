// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.speclang.translation;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Operator;

/**
 * Collects all axioms, which are created during the translation.
 * 
 */
public class AxiomCollector {

	private static final TermBuilder tb = TermBuilder.DF;
		
	private Map<Operator, Term> axioms = new LinkedHashMap<Operator, Term>();
	        
	public void collectAxiom(Operator n, Term a) {
		if (axioms.containsKey(n)) {
			axioms.put(n, (tb.and(axioms.get(n), a)));
		} else {
			axioms.put(n, a);
		}		
	}
		
	/**
	 * Returns all collected axioms.
	 * 
	 * @return Map from defined symbols to axioms
	 */
	public Map<Operator, Term> getAxioms() {
	    return axioms;
	}
}
