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
class BasicDependsSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {

    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        if (d.get(BasicSnippetData.Key.DEPENDENS) == null) {
            throw new UnsupportedOperationException(
                "Tried to produce a " + "depends-term for a contract without dependencies.");
        }
        assert JTerm.class.equals(BasicSnippetData.Key.DEPENDENS.getType());
        JTerm origDep = (JTerm) d.get(BasicSnippetData.Key.DEPENDENS);
        return replace(origDep, d.origVars, poVars.pre, d.tb);
    }
}
