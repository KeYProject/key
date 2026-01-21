package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * Interface for computing a cost for a given term or formula
 */
public interface TermFeature {

    RuleAppCost compute(Term term, Services services);
}
