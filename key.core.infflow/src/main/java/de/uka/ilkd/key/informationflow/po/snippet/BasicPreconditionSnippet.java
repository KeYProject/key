/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.informationflow.ProofObligationVars;
import de.uka.ilkd.key.logic.JTerm;

/**
 * Generate term "self != null".
 *
 * @author christoph
 */
class BasicPreconditionSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {
    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        if (d.get(BasicSnippetData.Key.PRECONDITION) == null) {
            throw new UnsupportedOperationException(
                "Tried to produce a " + "precondition for a contract without precondition.");
        }
        assert JTerm.class.equals(BasicSnippetData.Key.PRECONDITION.getType());
        JTerm origPre = (JTerm) d.get(BasicSnippetData.Key.PRECONDITION);
        return replace(origPre, d.origVars, poVars.pre, d.tb);
    }
}
