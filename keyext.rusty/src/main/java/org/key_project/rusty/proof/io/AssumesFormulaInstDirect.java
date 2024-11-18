/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.io;

import org.key_project.logic.LogicServices;
import org.key_project.prover.rules.AssumesFormulaInstantiation;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.SequentFormula;

/**
 * Instantiation of an if-formula that has to be proven by an explicit if-goal
 */
public class AssumesFormulaInstDirect implements AssumesFormulaInstantiation {
    /**
     * Simply the formula
     */
    private final SequentFormula sf;

    public AssumesFormulaInstDirect(SequentFormula sf) {
        this.sf = sf;
    }

    /**
     * @return the cf this is pointing to
     */
    @Override
    public SequentFormula getSequentFormula() {
        return sf;
    }

    public String toString() {
        return toString(null);
    }

    public boolean equals(Object p_obj) {
        if (!(p_obj instanceof AssumesFormulaInstDirect o)) {
            return false;
        }
        return sf.equals(o.sf);
    }

    public int hashCode() {
        int result = 17;
        result = 37 * result + sf.hashCode();
        return result;
    }

    @Override
    public String toString(LogicServices services) {
        return ProofSaver.printAnything(sf.formula(), (Services) services);
    }
}
