package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.LoopInvariant;


/**
 *
 *
 * @author christoph
 */
class SelfcomposedExecutionSnippet extends ReplaceAndRegisterMethod
        implements InfFlowFactoryMethod {

    @Override
    public Term produce(BasicSnippetData d,
                        ProofObligationVars poVars1,
                        ProofObligationVars poVars2)
            throws UnsupportedOperationException {
        BasicPOSnippetFactory f1 =
                POSnippetFactory.getBasicFactory(d, poVars1);
        BasicPOSnippetFactory f2 =
                POSnippetFactory.getBasicFactory(d, poVars2);

        final Term exec1 =
                f1.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_WITH_PRE_RELATION);
        final Term exec2 =
                f2.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_WITH_PRE_RELATION);
/*>>>>>>> 7f64f84cfbe7566c50d8bf4b6e6613a3a60fa3f6

        Term exec1 = d.tb.ff();
        Term exec2 = d.tb.ff();
        
        if (d.contract instanceof Contract) {
            exec1 = f1.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_WITH_PRE_RELATION);
            exec2 = f2.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_WITH_PRE_RELATION);
        } else if (d.contract instanceof LoopInvariant) {
            // KeYJavaType booleanKJT = d.tb.getServices().getTypeConverter().getBooleanType();
            // TODO: Here (or earlier) we should somehow add invariant and guard=true, but how?
            exec1 = //d.tb.and(((LoopInvariant) d.contract).getInternalInvariants().get(
                    //d.tb.getServices().getTypeConverter().getHeapLDT().getHeap()), ((LoopInvariant) d.contract).getLoop().getGuardExpression())
                f1.create(BasicPOSnippetFactory.Snippet.LOOP_CALL_WITH_INV_RELATION);
            exec2 = f2.create(BasicPOSnippetFactory.Snippet.LOOP_CALL_WITH_INV_RELATION);
            d.tb.getServices();
        }*/
        
        return d.tb.and(exec1, exec2);
    }
}
