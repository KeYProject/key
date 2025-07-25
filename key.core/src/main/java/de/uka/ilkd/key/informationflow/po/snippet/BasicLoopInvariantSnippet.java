/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

public class BasicLoopInvariantSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {

    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        if (d.get(BasicSnippetData.Key.LOOP_INVARIANT) == null) {
            throw new UnsupportedOperationException(
                "Tried to produce a " + "loop invariant for a loop without invariant.");
        }
        assert JTerm.class.equals(BasicSnippetData.Key.LOOP_INVARIANT_TERM.getType());
        JTerm origLoopInv = (JTerm) d.get(BasicSnippetData.Key.LOOP_INVARIANT_TERM);
        return replace(origLoopInv, d.origVars, poVars.pre, d.tb);
    }

}
