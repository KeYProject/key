/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;


/**
 *
 * @author christoph
 */
class BasicLoopExecutionWithInvariantSnippet extends ReplaceAndRegisterMethod
        implements FactoryMethod {

    @Override
    public Term produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        // generate snippet factory for symbolic execution
        BasicPOSnippetFactory symbExecFactory = POSnippetFactory.getBasicFactory(d, poVars);

        // loop invariant
        final Term freeInv = symbExecFactory.create(BasicPOSnippetFactory.Snippet.FREE_INV);
        final Term loopInv = symbExecFactory.create(BasicPOSnippetFactory.Snippet.LOOP_INV);
        final Term inv = d.tb.and(freeInv, loopInv);

        // symbolic execution
        Term symExec = symbExecFactory.create(BasicPOSnippetFactory.Snippet.LOOP_EXEC);


        // final symbolic execution term
        return d.tb.and(inv, symExec);
    }

}
