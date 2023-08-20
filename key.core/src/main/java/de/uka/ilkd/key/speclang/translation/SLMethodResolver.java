/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.translation;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.util.collection.ImmutableList;


/**
 * Resolver for method calls in specifications.
 */
public final class SLMethodResolver extends SLExpressionResolver {

    public SLMethodResolver(JavaInfo javaInfo, SLResolverManager manager, KeYJavaType specInClass) {
        super(javaInfo, manager, specInClass);
    }


    @Override
    protected boolean canHandleReceiver(SLExpression receiver) {
        return receiver != null && !receiver.getType().getFullName().endsWith("[]");
    }


    @Override
    protected SLExpression doResolving(SLExpression receiver, String methodName,
            SLParameters parameters) throws SLTranslationException {

        if (parameters == null || !parameters.isListOfTerm()) {
            return null;
        }

        // FIXME weigl this seems wrong. Should it not be that this
        // containingType=manager.specInClass?
        KeYJavaType containingType = receiver.getType();
        if (containingType == null) {
            return null;
        }
        ImmutableList<SLExpression> ps = parameters.getParameters();
        for (LocationVariable h : HeapContext.getModHeaps(services, false)) {
            while (ps.size() > 0
                    && ps.head().getTerm().op().name().toString().startsWith(h.name().toString())) {
                ps = ps.tail();
            }
        }

        ImmutableList<KeYJavaType> signature =
            new SLParameters(ps).getSignature(javaInfo.getServices());

        IProgramMethod pm = null;
        Term recTerm = receiver.getTerm();

        while (true) {
            pm = javaInfo.getToplevelPM(containingType, methodName, signature);

            LocationVariable et = (LocationVariable) javaInfo
                    .getAttribute(ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, containingType);
            if (et != null && pm == null) {
                containingType = et.getKeYJavaType();
                if (recTerm != null) {
                    final Function fieldSymbol =
                        services.getTypeConverter().getHeapLDT().getFieldSymbolForPV(et, services);
                    recTerm = services.getTermBuilder().dot(et.sort(), recTerm, fieldSymbol);
                }
            } else {
                break;
            }
        }

        if (pm == null) {
            return null;
        }

        List<LocationVariable> heaps = new ArrayList<>();
        int hc = 0;
        for (LocationVariable h : HeapContext.getModHeaps(services, false)) {
            if (hc >= pm.getHeapCount(services)) {
                break;
            }
            heaps.add(h);
        }
        ImmutableList<SLExpression> params = parameters.getParameters();
        int i = 0;
        Term[] subs = new Term[params.size() - pm.getHeapCount(services)
                + pm.getStateCount() * pm.getHeapCount(services) + (pm.isStatic() ? 0 : 1)];
        for (LocationVariable heap : heaps) {
            if (pm.getStateCount() >= 1) {
                subs[i++] = services.getTermBuilder().var(heap);
                if (pm.getStateCount() == 2) {
                    subs[i++] = params.head().getTerm();
                }
            }
            params = params.tail();
        }

        if (!pm.isStatic()) {
            if (!receiver.isTerm()) {
                throw manager.excManager.createException("non-static method (" + methodName
                    + ") invocation" + " on Type " + receiver.getType());
            }
            subs[i++] = recTerm;
        }

        for (SLExpression slExpression : params) {
            // Remember: parameters.isLisOfTerm() is true!
            final Term term = slExpression.getTerm();
            subs[i] = term.sort() == Sort.FORMULA ? services.getTermBuilder().convertToBoolean(term)
                    : term;
            i++;
        }

        if (pm.isVoid()) {
            throw manager.excManager.createException(
                "can not use void " + "method \"" + methodName + "\" in specification expression.");
        }

        return new SLExpression(services.getTermBuilder().tf().createTerm(pm, subs),
            pm.getReturnType());
    }

}
