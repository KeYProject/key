/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

/**
 * Generate term "self != null".
 *
 * @author christoph
 */
class BasicPostconditionSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {

    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        if (d.get(BasicSnippetData.Key.POSTCONDITION) == null) {
            throw new UnsupportedOperationException(
                "Tried to produce a " + "postcondition for a contract without postcondition.");
        }
        assert JTerm.class.equals(BasicSnippetData.Key.POSTCONDITION.getType());
        JTerm origPost = (JTerm) d.get(BasicSnippetData.Key.POSTCONDITION);
        return replace(origPost, d.origVars, poVars.post, d.tb);
    }
}
