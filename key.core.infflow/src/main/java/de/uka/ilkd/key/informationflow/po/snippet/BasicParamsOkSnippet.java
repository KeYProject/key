/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.informationflow.ProofObligationVars;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.jspecify.annotations.NullMarked;

/**
 * Generate conjunction of... - "p_i.<created> = TRUE | p_i = null" for object parameters, and -
 * "inBounds(p_i)" for integer parameters
 *
 * @author christoph
 */
@NullMarked
class BasicParamsOkSnippet implements FactoryMethod {

    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        JTerm paramsOK = d.tb.tt();
        for (JTerm param : poVars.pre.localVars) {
            if (!(param.op() instanceof ProgramVariable pv)) {
                throw new UnsupportedOperationException(
                    "Tried to produce " + "PARAMS_OK for a term " + "which is no ProgramVariable.");
            }
            paramsOK = d.tb.and(paramsOK, d.tb.reachableValue(poVars.pre.heap, param,
                requireKeYJavaType(pv)));
        }
        if (poVars.pre.guard != null) {
            if (!(poVars.pre.guard.op() instanceof ProgramVariable pv)) {
                throw new UnsupportedOperationException(
                    "Tried to produce " + "PARAMS_OK for a term " + "which is no ProgramVariable.");
            }
            paramsOK = d.tb.and(paramsOK, d.tb.reachableValue(poVars.pre.heap, poVars.pre.guard,
                requireKeYJavaType(pv)));
        }
        return paramsOK;
    }

    private static KeYJavaType requireKeYJavaType(ProgramVariable pv) {
        final KeYJavaType kjt = pv.getKeYJavaType();
        if (kjt == null) {
            throw new NullPointerException("No KeYJavaType for the variable " + pv + ".");
        }
        return kjt;
    }
}
