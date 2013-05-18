/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.ProofObligationVars;

/**
 * Generate term "MyClass::exactInstance(self) = TRUE".
 *
 * @author christoph
 */
class BasicSelfExactTypeSnippet implements FactoryMethod {

    @Override
    public Term produce(BasicSnippetData d,
                        ProofObligationVars poVars)
            throws UnsupportedOperationException {
        IObserverFunction targetMethod =
                (IObserverFunction) d.get(BasicSnippetData.Key.TARGET_METHOD);
        if (!(targetMethod instanceof IProgramMethod)) {
            throw new UnsupportedOperationException("Tried to produce "
                    + "SELF_EXACT_TYPE for an observer "
                    + "which is no IProgramMethod.");
        }
        final IProgramMethod pm = (IProgramMethod) targetMethod;
        KeYJavaType forClass = (KeYJavaType) d.get(BasicSnippetData.Key.FOR_CLASS);
        Term result = d.tb.tt();
        if (forClass != null) {
            final Sort contractSort = forClass.getSort();
            result = (poVars.pre.self == null || pm.isConstructor())
                    ? d.tb.tt() : d.tb.exactInstance(contractSort, poVars.pre.self);
        } else if (d.get(BasicSnippetData.Key.LOOP_INVARIANT_TERM) != null) {
            final Sort loopInvSort= pm.sort();
            result = (poVars.pre.self == null || pm.isConstructor())
                    ? d.tb.tt() : d.tb.exactInstance(loopInvSort, poVars.pre.self);
        }
        return result;
    }
}
