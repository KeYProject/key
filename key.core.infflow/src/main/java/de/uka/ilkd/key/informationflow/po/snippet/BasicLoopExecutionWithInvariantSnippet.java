/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.informationflow.ProofObligationVars;
import de.uka.ilkd.key.logic.JTerm;


/**
 *
 * @author christoph
 */
class BasicLoopExecutionWithInvariantSnippet extends ReplaceAndRegisterMethod
        implements FactoryMethod {

    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        // generate snippet factory for symbolic execution
        BasicPOSnippetFactory symbExecFactory = POSnippetFactory.getBasicFactory(d, poVars);

        // loop invariant
        final JTerm freeInv = symbExecFactory.create(BasicPOSnippetFactory.Snippet.FREE_INV);
        final JTerm loopInv = symbExecFactory.create(BasicPOSnippetFactory.Snippet.LOOP_INV);
        final JTerm inv = d.tb.and(freeInv, loopInv);

        // symbolic execution
        JTerm symExec = symbExecFactory.create(BasicPOSnippetFactory.Snippet.LOOP_EXEC);


        // final symbolic execution term
        return d.tb.and(inv, symExec);
    }

}
