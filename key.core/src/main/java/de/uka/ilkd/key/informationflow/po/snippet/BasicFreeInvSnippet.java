/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

public class BasicFreeInvSnippet implements FactoryMethod {

    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        BasicPOSnippetFactory f = POSnippetFactory.getBasicFactory(d, poVars);

        // "wellformed(heapAtPre)"
        final JTerm wellFormed = d.tb.wellFormed(poVars.pre.heap);

        // "heap == heapAtPre"
        final JTerm eqHeapAndHeapAtPre = d.tb.equals(d.tb.getBaseHeap(), poVars.pre.heap);

        // "self != null"
        final JTerm selfNotNull = f.create(BasicPOSnippetFactoryImpl.Snippet.SELF_NOT_NULL);

        // "self.<created> = TRUE"
        final JTerm selfCreated = f.create(BasicPOSnippetFactoryImpl.Snippet.SELF_CREATED);

        // "MyClass::exactInstance(self) = TRUE"
        final JTerm selfExactType = f.create(BasicPOSnippetFactoryImpl.Snippet.SELF_EXACT_TYPE);

        // conjunction of...
        // - "p_i.<created> = TRUE | p_i = null" for object parameters, and
        // - "inBounds(p_i)" for integer parameters
        JTerm paramsOK = f.create(BasicPOSnippetFactoryImpl.Snippet.PARAMS_OK);

        return d.tb.and(wellFormed, eqHeapAndHeapAtPre, selfNotNull, selfCreated, selfExactType,
            paramsOK);
    }
}
