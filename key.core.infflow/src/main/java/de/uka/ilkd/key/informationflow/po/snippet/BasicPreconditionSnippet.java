/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.informationflow.ProofObligationVars;
import de.uka.ilkd.key.logic.JTerm;

import org.jspecify.annotations.NullMarked;

/**
 * Generate term "self != null".
 *
 * @author christoph
 */
@NullMarked
class BasicPreconditionSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {
    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        final Object preObj = d.get(BasicSnippetData.Key.PRECONDITION);
        if (preObj == null) {
            throw new UnsupportedOperationException(
                "Tried to produce a " + "precondition for a contract without precondition.");
        }
        assert JTerm.class.equals(BasicSnippetData.Key.PRECONDITION.getType());
        final JTerm origPre = (JTerm) preObj;
        return replace(origPre, d.origVars, poVars.pre, d.tb);
    }
}
