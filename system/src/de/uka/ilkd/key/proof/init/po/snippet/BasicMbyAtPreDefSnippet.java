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
class BasicMbyAtPreDefSnippet extends ReplaceAndRegisterMethod
        implements FactoryMethod {

    @Override
    public Term produce(BasicSnippetData d,
                        ProofObligationVars poVars)
            throws UnsupportedOperationException {
        if (!d.hasMby) {
            return d.tb.tt();
        }

        if (d.get(BasicSnippetData.Key.MEASURED_BY) == null) {
            throw new UnsupportedOperationException("Tried to produce a "
                    + "measured_by for a contract without measured_by "
                    + "(though the contract pretends to have one).");
        }
        assert Term.class.equals(BasicSnippetData.Key.MEASURED_BY.getType());
        final Term origMby =
                (Term) d.get(BasicSnippetData.Key.MEASURED_BY);
        final Term mby = replace(origMby, d.origVars, poVars.pre, d.tb);

        return d.tb.equals(poVars.pre.mbyAtPre, mby);
    }
}
