package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

public class SelfcomposedLoopSnippet extends ReplaceAndRegisterMethod implements
        InfFlowFactoryMethod {

    @Override
    public Term produce(BasicSnippetData d, ProofObligationVars poVars1,
            ProofObligationVars poVars2) throws UnsupportedOperationException {
        BasicPOSnippetFactory f1 =
                POSnippetFactory.getBasicFactory(d, poVars1);
        BasicPOSnippetFactory f2 =
                POSnippetFactory.getBasicFactory(d, poVars2);
        // TODO: Here (or earlier) we should (really?) somehow add guard=true, but how?
        final Term exec1 =
                f1.create(BasicPOSnippetFactory.Snippet.LOOP_CALL_WITH_INV_RELATION);
        final Term exec2 =
                f2.create(BasicPOSnippetFactory.Snippet.LOOP_CALL_WITH_INV_RELATION);

        return d.tb.and(exec1, exec2);
    }
}