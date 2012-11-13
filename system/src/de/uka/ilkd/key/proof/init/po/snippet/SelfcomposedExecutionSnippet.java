package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;


/**
 *
 *
 * @author christoph
 */
class SelfcomposedExecutionSnippet extends ReplaceAnRegisterMethod
        implements InfFlowFactoryMethod {

    @Override
    public Term produce(BasicSnippetData d,
                        ProofObligationVars poVars1,
                        ProofObligationVars poVars2)
            throws UnsupportedOperationException {
        BasicPOSnippetFactory f1 =
                POSinppetFactory.getBasicFactory(d, poVars1);
        BasicPOSnippetFactory f2 =
                POSinppetFactory.getBasicFactory(d, poVars2);

        final Term exec1 =
                f1.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_WITH_PRE_RELATION);
        final Term exec2 =
                f2.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_WITH_PRE_RELATION);

        return d.tb.and(exec1, exec2);
    }
}
