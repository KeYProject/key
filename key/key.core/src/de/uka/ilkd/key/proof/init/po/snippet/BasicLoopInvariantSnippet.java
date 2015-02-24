package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

public class BasicLoopInvariantSnippet extends ReplaceAndRegisterMethod
        implements FactoryMethod {

    @Override
    public Term produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        if (d.get(BasicSnippetData.Key.LOOP_INVARIANT) == null) {
            throw new UnsupportedOperationException("Tried to produce a "
                    + "loop invariant for a loop without invariant.");
        }
        assert Term.class.equals(BasicSnippetData.Key.LOOP_INVARIANT_TERM.getType());
        Term origLoopInv = (Term) d.get(
                BasicSnippetData.Key.LOOP_INVARIANT_TERM);
        return replace(origLoopInv, d.origVars, poVars.pre, d.tb);
    }

}