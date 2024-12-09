/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.io.ProofSaver;


/**
 * Instantiation of an if-formula that has to be proven by an explicit if-goal
 */

public class IfFormulaInstDirect implements IfFormulaInstantiation {

    /**
     * Simply the formula
     */
    private final SequentFormula cf;

    public IfFormulaInstDirect(SequentFormula p_cf) {
        cf = p_cf;
    }

    /**
     * @return the cf this is pointing to
     */
    public SequentFormula getConstrainedFormula() {
        return cf;
    }

    public String toString() {
        return toString(null);
    }

    public boolean equals(Object p_obj) {
        if (!(p_obj instanceof IfFormulaInstDirect)) {
            return false;
        }
        return cf.equals(((IfFormulaInstDirect) p_obj).cf);
    }

    public int hashCode() {
        int result = 17;
        result = 37 * result + cf.hashCode();
        return result;
    }

    public String toString(Services services) {
        return ProofSaver.printAnything(cf.formula(), services);
    }
}
