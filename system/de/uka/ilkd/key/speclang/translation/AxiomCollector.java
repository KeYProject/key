package de.uka.ilkd.key.speclang.translation;

import java.util.LinkedHashMap;
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
		
	private Map /*Named -> Term */ axioms = new LinkedHashMap();
	
        
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
