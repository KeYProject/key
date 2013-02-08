/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

/**
 * Generate conjunction of...
 * - "p_i.<created> = TRUE | p_i = null" for object parameters, and
 * - "inBounds(p_i)" for integer parameters
 *
 * @author christoph
 */
class BasicParamsOkSnippet implements FactoryMethod {

    @Override
    public Term produce(BasicSnippetData d,
                        ProofObligationVars poVars)
            throws UnsupportedOperationException {
        Term paramsOK = d.tb.tt();
        for (Term param : poVars.localIns) {
            if (!(param.op() instanceof ProgramVariable)) {
                throw new UnsupportedOperationException("Tried to produce "
                        + "PARAMS_OK for a term "
                        + "which is no ProgramVariable.");
            }
            ProgramVariable pv = (ProgramVariable) param.op();
            paramsOK = d.tb.and(paramsOK, d.tb.reachableValue(poVars.heap, param, pv.getKeYJavaType()));
        }
        for (Term param : poVars.localOuts) {
            if (!(param.op() instanceof ProgramVariable)) {
                throw new UnsupportedOperationException("Tried to produce "
                        + "PARAMS_OK for a term "
                        + "which is no ProgramVariable.");
            }
            ProgramVariable pv = (ProgramVariable) param.op();
            paramsOK = d.tb.and(paramsOK, d.tb.reachableValue(poVars.heap, param, pv.getKeYJavaType()));
        }
        if (poVars.guard != null) {
            if (!(poVars.guard.op() instanceof ProgramVariable)) {
                throw new UnsupportedOperationException("Tried to produce "
                        + "PARAMS_OK for a term "
                        + "which is no ProgramVariable.");
            }
            ProgramVariable pv = (ProgramVariable) poVars.guard.op();
            paramsOK = d.tb.and(paramsOK, d.tb.reachableValue(poVars.heap, poVars.guard, pv.getKeYJavaType()));
        }
        if (poVars.guardAtPost != null) {
            if (!(poVars.guardAtPost.op() instanceof ProgramVariable)) {
                throw new UnsupportedOperationException("Tried to produce "
                        + "PARAMS_OK for a term "
                        + "which is no ProgramVariable.");
            }
            ProgramVariable pv = (ProgramVariable) poVars.guardAtPost.op();
            paramsOK = d.tb.and(paramsOK, d.tb.reachableValue(poVars.heap, poVars.guardAtPost, pv.getKeYJavaType()));
        }
        return paramsOK;
    }
}
