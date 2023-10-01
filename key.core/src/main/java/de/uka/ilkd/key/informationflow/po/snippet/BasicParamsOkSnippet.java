/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

/**
 * Generate conjunction of... - "p_i.<created> = TRUE | p_i = null" for object parameters, and -
 * "inBounds(p_i)" for integer parameters
 *
 * @author christoph
 */
class BasicParamsOkSnippet implements FactoryMethod {

    @Override
    public Term produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        Term paramsOK = d.tb.tt();
        for (Term param : poVars.pre.localVars) {
            if (!(param.op() instanceof ProgramVariable pv)) {
                throw new UnsupportedOperationException(
                    "Tried to produce " + "PARAMS_OK for a term " + "which is no ProgramVariable.");
            }
            paramsOK = d.tb.and(paramsOK,
                d.tb.reachableValue(poVars.pre.heap, param, pv.getKeYJavaType()));
        }
        if (poVars.pre.guard != null) {
            if (!(poVars.pre.guard.op() instanceof ProgramVariable pv)) {
                throw new UnsupportedOperationException(
                    "Tried to produce " + "PARAMS_OK for a term " + "which is no ProgramVariable.");
            }
            paramsOK = d.tb.and(paramsOK,
                d.tb.reachableValue(poVars.pre.heap, poVars.pre.guard, pv.getKeYJavaType()));
        }
        return paramsOK;
    }
}
