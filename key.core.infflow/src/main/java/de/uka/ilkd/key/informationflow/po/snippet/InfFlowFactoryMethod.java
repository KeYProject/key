/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.informationflow.ProofObligationVars;
import de.uka.ilkd.key.logic.JTerm;

/**
 * @author christoph
 */
interface InfFlowFactoryMethod {

    JTerm produce(BasicSnippetData d, ProofObligationVars poVars1, ProofObligationVars poVars2)
            throws UnsupportedOperationException;
}
