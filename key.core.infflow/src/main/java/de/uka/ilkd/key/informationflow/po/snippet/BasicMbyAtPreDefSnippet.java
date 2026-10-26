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
class BasicMbyAtPreDefSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {

    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        if (!d.hasMby) {
            return d.tb.tt();
        }

        final Object mbyObj = d.get(BasicSnippetData.Key.MEASURED_BY);
        if (mbyObj == null) {
            throw new UnsupportedOperationException(
                "Tried to produce a " + "measured_by for a contract without measured_by "
                    + "(though the contract pretends to have one).");
        }
        assert JTerm.class.equals(BasicSnippetData.Key.MEASURED_BY.getType());
        final JTerm origMby = (JTerm) mbyObj;
        final JTerm mby = replace(origMby, d.origVars, poVars.pre, d.tb);

        final JTerm mbyAtPre = poVars.pre.mbyAtPre;
        if (mbyAtPre == null) {
            throw new NullPointerException(
                "No measured-by-at-pre term although the contract has a measured-by clause.");
        }
        return d.tb.equals(mbyAtPre, mby);
    }
}
