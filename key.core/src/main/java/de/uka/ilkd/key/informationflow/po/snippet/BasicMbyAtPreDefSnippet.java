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
class BasicMbyAtPreDefSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {

    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        if (!d.hasMby) {
            return d.tb.tt();
        }

        if (d.get(BasicSnippetData.Key.MEASURED_BY) == null) {
            throw new UnsupportedOperationException(
                "Tried to produce a " + "measured_by for a contract without measured_by "
                    + "(though the contract pretends to have one).");
        }
        assert JTerm.class.equals(BasicSnippetData.Key.MEASURED_BY.getType());
        final JTerm origMby = (JTerm) d.get(BasicSnippetData.Key.MEASURED_BY);
        final JTerm mby = replace(origMby, d.origVars, poVars.pre, d.tb);

        return d.tb.equals(poVars.pre.mbyAtPre, mby);
    }
}
