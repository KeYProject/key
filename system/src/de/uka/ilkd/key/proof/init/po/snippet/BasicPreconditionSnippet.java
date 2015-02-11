/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

/**
 * Generate term "self != null".
 *
 * @author christoph
 */
class BasicPreconditionSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {

    @Override
    public Term produce(BasicSnippetData d,
                        ProofObligationVars poVars)
            throws UnsupportedOperationException {
        if (d.get(BasicSnippetData.Key.PRECONDITION) == null) {
            throw new UnsupportedOperationException("Tried to produce a "
                    + "precondition for a contract without precondition.");
        }
        assert Term.class.equals(BasicSnippetData.Key.PRECONDITION.getType());
        Term origPre = (Term) d.get(
                BasicSnippetData.Key.PRECONDITION);
        return replace(origPre, d.origVars, poVars.pre, d.tb);
    }
}