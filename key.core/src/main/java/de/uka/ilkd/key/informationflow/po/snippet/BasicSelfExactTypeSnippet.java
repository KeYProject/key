/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

import org.key_project.logic.sort.Sort;

/**
 * Generate term "MyClass::exactInstance(self) = TRUE".
 *
 * @author christoph
 */
class BasicSelfExactTypeSnippet implements FactoryMethod {

    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        IObserverFunction targetMethod =
            (IObserverFunction) d.get(BasicSnippetData.Key.TARGET_METHOD);
        if (!(targetMethod instanceof IProgramMethod pm)) {
            throw new UnsupportedOperationException("Tried to produce "
                + "SELF_EXACT_TYPE for an observer " + "which is no IProgramMethod.");
        }
        KeYJavaType forClass = (KeYJavaType) d.get(BasicSnippetData.Key.FOR_CLASS);
        JTerm result = d.tb.tt();
        if (forClass != null) {
            final Sort contractSort = forClass.getSort();
            result = (poVars.pre.self == null || pm.isConstructor()) ? d.tb.tt()
                    : d.tb.exactInstance(contractSort, poVars.pre.self);
        } else if (d.get(BasicSnippetData.Key.LOOP_INVARIANT_TERM) != null) {
            final Sort loopInvSort = pm.sort();
            result = (poVars.pre.self == null || pm.isConstructor()) ? d.tb.tt()
                    : d.tb.exactInstance(loopInvSort, poVars.pre.self);
        }
        return result;
    }
}
