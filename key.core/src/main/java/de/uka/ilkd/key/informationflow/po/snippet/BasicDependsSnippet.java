/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

/**
 * Generate term "self != null".
 *
 * @author christoph
 */
class BasicDependsSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {

    @Override
    public Term produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        if (d.get(BasicSnippetData.Key.DEPENDENS) == null) {
            throw new UnsupportedOperationException(
                "Tried to produce a " + "depends-term for a contract without dependencies.");
        }
        assert Term.class.equals(BasicSnippetData.Key.DEPENDENS.getType());
        Term origDep = (Term) d.get(BasicSnippetData.Key.DEPENDENS);
        return replace(origDep, d.origVars, poVars.pre, d.tb);
    }
}
