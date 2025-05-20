/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

import org.jspecify.annotations.NonNull;


/**
 *
 *
 * @author christoph
 */
class InfFlowContractAppSnippet extends ReplaceAndRegisterMethod implements InfFlowFactoryMethod {

    @Override
    public @NonNull Term produce(@NonNull BasicSnippetData d, @NonNull ProofObligationVars poVars1,
            @NonNull ProofObligationVars poVars2) throws UnsupportedOperationException {
        BasicPOSnippetFactory f1 = POSnippetFactory.getBasicFactory(d, poVars1);
        BasicPOSnippetFactory f2 = POSnippetFactory.getBasicFactory(d, poVars2);

        Term preCond1 = f1.create(BasicPOSnippetFactory.Snippet.CONTRACT_PRE);
        Term preCond2 = f2.create(BasicPOSnippetFactory.Snippet.CONTRACT_PRE);


        InfFlowPOSnippetFactory iff = POSnippetFactory.getInfFlowFactory(d, poVars1, poVars2);
        Term inOutRelations =
            iff.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_CONTRACT_APP_INOUT_RELATION);

        return d.tb.imp(d.tb.and(preCond1, preCond2), inOutRelations);
    }
}
