/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

/**
 * Generate term "self != null".
 *
 * @author christoph
 */
class BasicSelfCreatedSnippet implements FactoryMethod {

    @Override
    public Term produce(BasicSnippetData d,
                        ProofObligationVars poVars)
            throws UnsupportedOperationException {
        if (!(d.target instanceof IProgramMethod)) {
            throw new UnsupportedOperationException("Tried to produce "
                    + "SELF_CREATED for an observer "
                    + "which is no IProgramMethod.");
        }
        final IProgramMethod pm = (IProgramMethod) d.target;
        return (poVars.self == null || pm.isConstructor())
               ? d.tb.tt() : d.tb.created(poVars.self);
    }
}
