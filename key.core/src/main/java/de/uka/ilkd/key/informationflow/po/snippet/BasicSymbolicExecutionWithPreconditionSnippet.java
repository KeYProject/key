/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.informationflow.po.snippet.BasicSnippetData.Key;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;


/**
 *
 * @author christoph
 */
class BasicSymbolicExecutionWithPreconditionSnippet extends ReplaceAndRegisterMethod
        implements FactoryMethod {

    @Override
    public Term produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        // generate snippet factory for symbolic execution
        BasicPOSnippetFactory symbExecFactory = POSnippetFactory.getBasicFactory(d, poVars);

        // precondition
        final Term pre;

        final Term freePre = symbExecFactory.create(BasicPOSnippetFactory.Snippet.FREE_PRE);
        final Term contractPre = symbExecFactory.create(BasicPOSnippetFactory.Snippet.CONTRACT_PRE);

        Term freeReq = (Term) d.get(Key.FREE_PRECONDITION);
        if (freeReq != null) {
            freeReq = replace(freeReq, d.origVars, poVars.pre, d.tb);
            pre = d.tb.and(freePre, freeReq, contractPre);
        } else {
            pre = d.tb.and(freePre, contractPre);
        }

        // symbolic execution
        final Term symExec = symbExecFactory.create(BasicPOSnippetFactory.Snippet.SYMBOLIC_EXEC);

        // final symbolic execution term
        return d.tb.and(pre, symExec);
    }

}
