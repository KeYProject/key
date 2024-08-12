package org.key_project.rusty.rule;

import org.key_project.rusty.Services;
import org.key_project.rusty.logic.SequentFormula;

public interface IfFormulaInstantiation {
    /**
     * @return the cf this is pointing to
     */
    SequentFormula getConstrainedFormula();

    String toString(Services services);
}
