/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.informationflow.ProofObligationVars;
import de.uka.ilkd.key.logic.JTerm;

import org.jspecify.annotations.NullMarked;

@NullMarked
public class BasicLoopInvariantSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {

    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        final Object loopInvObj = d.get(BasicSnippetData.Key.LOOP_INVARIANT_TERM);
        if (loopInvObj == null) {
            throw new UnsupportedOperationException(
                "Tried to produce a " + "loop invariant for a loop without invariant.");
        }
        assert JTerm.class.equals(BasicSnippetData.Key.LOOP_INVARIANT_TERM.getType());
        final JTerm origLoopInv = (JTerm) loopInvObj;
        return replace(origLoopInv, d.origVars, poVars.pre, d.tb);
    }

}
