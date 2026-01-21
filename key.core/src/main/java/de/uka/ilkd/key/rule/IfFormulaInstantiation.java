package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;


/*
 * This interface represents objects representing an instantiation of one formula of the if-sequence
 * of a taclet.
 */

public interface IfFormulaInstantiation {

    /**
     * @return the cf this is pointing to
     */
    SequentFormula getConstrainedFormula();

    String toString(Services services);
}
