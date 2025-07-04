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
class BasicModifiableSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {

    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        if (d.get(BasicSnippetData.Key.MODIFIABLE) == null) {
            throw new UnsupportedOperationException(
                "Tried to produce a " + "modifiable-term for a contract without modifiable.");
        }
        assert JTerm.class.equals(BasicSnippetData.Key.MODIFIABLE.getType());
        JTerm origModifiable = (JTerm) d.get(BasicSnippetData.Key.MODIFIABLE);
        return replace(origModifiable, d.origVars, poVars.pre, d.tb);
    }
}
