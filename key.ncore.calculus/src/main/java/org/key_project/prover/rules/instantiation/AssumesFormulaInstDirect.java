/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.instantiation;


import org.key_project.logic.LogicServices;
import org.key_project.prover.sequent.SequentFormula;


/// Instantiation of an assumes-formula that has to be proven by an explicit assumes-goal
///
/// This is used if an assumes sequent cannot be matched against an existing formula in the
/// proof goal. The instantiation is usually provided by the user or the proof search strategy.
///
///
/// Application of a taclet whose instantiations contain a direct instantiation leads to a proof
/// split
/// where on one branch the formula used as instantiation has to be proven valid.
///
///
/// @see AssumesFormulaInstantiation, AssumesFormulaInstSeq
public class AssumesFormulaInstDirect implements AssumesFormulaInstantiation {

    /// Simply the formula
    private final SequentFormula cf;

    public AssumesFormulaInstDirect(SequentFormula p_cf) {
        cf = p_cf;
    }

    /// @return the cf this is pointing to
    public SequentFormula getSequentFormula() {
        return cf;
    }

    public String toString() {
        return toString(null);
    }

    public boolean equals(Object p_obj) {
        if (!(p_obj instanceof AssumesFormulaInstDirect)) {
            return false;
        }
        return cf.equals(((AssumesFormulaInstDirect) p_obj).cf);
    }

    public int hashCode() {
        int result = 17;
        result = 37 * result + cf.hashCode();
        return result;
    }

    public String toString(LogicServices services) {
        return cf.toString();
    }
}
