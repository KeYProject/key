/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

/**
 * Generate term "self != null".
 *
 * @author christoph
 */
class BasicParamsOkSnippet implements FactoryMethod {

    @Override
    public Term produce(BasicPOSnippetFactory f,
                        BasicSnippetData d,
                        ProofObligationVars poVars)
            throws UnsupportedOperationException {
        Term paramsOK = d.tb.tt();
        for (Term param : poVars.params) {
            if (param.op() instanceof ProgramVariable) {
                throw new UnsupportedOperationException("Tried to produce "
                        + "PARAMS_OK for an term "
                        + "which is no ProgramVariable.");
            }
            ProgramVariable pv = (ProgramVariable) param.op();
            paramsOK = d.tb.and(paramsOK, d.tb.reachableValue(pv));
        }
        return paramsOK;
    }
}
