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
class BasicPostconditionSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {

    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        final Object postObj = d.get(BasicSnippetData.Key.POSTCONDITION);
        if (postObj == null) {
            throw new UnsupportedOperationException(
                "Tried to produce a " + "postcondition for a contract without postcondition.");
        }
        assert JTerm.class.equals(BasicSnippetData.Key.POSTCONDITION.getType());
        final JTerm origPost = (JTerm) postObj;
        return replace(origPost, d.origVars, poVars.post, d.tb);
    }
}
