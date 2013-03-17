package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

public class BasicFreeInvSnippet implements FactoryMethod {

    @Override
    public Term produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        BasicPOSnippetFactory f =
                POSnippetFactory.getBasicFactory(d, poVars);
        
        // "wellformed(heap)"
        final Term wellFormed = d.tb.wellFormed(poVars.heap);
        
        // "heap == heapAtPre"
        final Term eqHeapAndHeapAtPre =
                poVars.heapAtPre != null ?
                d.tb.equals(poVars.heap, poVars.heapAtPre) :
                d.tb.tt();
                
        // "self != null"
        final Term selfNotNull = f.create(
                BasicPOSnippetFactoryImpl.Snippet.SELF_NOT_NULL);
        
        // "self.<created> = TRUE"
        final Term selfCreated = f.create(
                BasicPOSnippetFactoryImpl.Snippet.SELF_CREATED);
        
        // "MyClass::exactInstance(self) = TRUE"
        final Term selfExactType = f.create(
                BasicPOSnippetFactoryImpl.Snippet.SELF_EXACT_TYPE);
        
        // conjunction of...
        // - "p_i.<created> = TRUE | p_i = null" for object parameters, and
        // - "inBounds(p_i)" for integer parameters
        Term paramsOK = f.create(BasicPOSnippetFactoryImpl.Snippet.PARAMS_OK);
        
        return d.tb.and(wellFormed, eqHeapAndHeapAtPre, selfNotNull, selfCreated,
                selfExactType, paramsOK);
    }
}
