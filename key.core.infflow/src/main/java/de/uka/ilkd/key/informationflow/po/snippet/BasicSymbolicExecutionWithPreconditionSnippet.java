/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.informationflow.ProofObligationVars;
import de.uka.ilkd.key.informationflow.po.snippet.BasicSnippetData.Key;
import de.uka.ilkd.key.logic.JTerm;


/**
 *
 * @author christoph
 */
class BasicSymbolicExecutionWithPreconditionSnippet extends ReplaceAndRegisterMethod
        implements FactoryMethod {

    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        // generate snippet factory for symbolic execution
        BasicPOSnippetFactory symbExecFactory = POSnippetFactory.getBasicFactory(d, poVars);

        // precondition
        final JTerm pre;

        final JTerm freePre = symbExecFactory.create(BasicPOSnippetFactory.Snippet.FREE_PRE);
        final JTerm contractPre =
            symbExecFactory.create(BasicPOSnippetFactory.Snippet.CONTRACT_PRE);

        JTerm freeReq = (JTerm) d.get(Key.FREE_PRECONDITION);
        if (freeReq != null) {
            freeReq = replace(freeReq, d.origVars, poVars.pre, d.tb);
            pre = d.tb.and(freePre, freeReq, contractPre);
        } else {
            pre = d.tb.and(freePre, contractPre);
        }

        // symbolic execution
        final JTerm symExec = symbExecFactory.create(BasicPOSnippetFactory.Snippet.SYMBOLIC_EXEC);

        // final symbolic execution term
        return d.tb.and(pre, symExec);
    }

}
