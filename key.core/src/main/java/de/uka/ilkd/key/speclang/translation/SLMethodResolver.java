/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.translation;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.transformations.pipeline.PipelineConstants;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.logic.op.Function;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 * Resolver for method calls in specifications.
 */
@NullMarked
public final class SLMethodResolver extends SLExpressionResolver {

    public SLMethodResolver(JavaInfo javaInfo, SLResolverManager manager, KeYJavaType specInClass) {
        super(javaInfo, manager, specInClass);
    }


    @Override
    protected boolean canHandleReceiver(@Nullable SLExpression receiver) {
        return receiver != null
                && !Objects.requireNonNull(receiver.getType(), "no receiver type")
                        .getFullName().endsWith("[]");
    }


    @Override
    protected @Nullable SLExpression doResolving(@Nullable SLExpression receiver, String methodName,
            @Nullable SLParameters parameters) throws SLTranslationException {

        if (parameters == null || !parameters.isListOfTerm()) {
            return null;
        }

        SLExpression recv = Objects.requireNonNull(receiver, "no receiver");
        KeYJavaType containingType = recv.getType();
        if (containingType == null) {
            return null;
        }
        ImmutableList<SLExpression> ps = parameters.parameters();
        for (LocationVariable h : HeapContext.getModifiableHeaps(services, false)) {
            while (ps.size() > 0 && Objects.requireNonNull(ps.head().getTerm(), "no term")
                    .op().name().toString().startsWith(h.name().toString())) {
                ps = ps.tail();
            }
        }

        ImmutableList<KeYJavaType> signature =
            new SLParameters(ps).getSignature(javaInfo.getServices());

        IProgramMethod pm = null;
        JTerm recTerm = recv.getTerm();

        while (true) {
            pm = javaInfo.getToplevelPM(
                Objects.requireNonNull(containingType, "no containing type"),
                methodName, signature);

            LocationVariable et = (LocationVariable) javaInfo
                    .getAttribute(PipelineConstants.IMPLICIT_ENCLOSING_THIS, containingType);
            if (et != null && pm == null) {
                containingType =
                    Objects.requireNonNull(et.getKeYJavaType(), "no enclosing-class type");
                if (recTerm != null) {
                    final Function fieldSymbol = Objects
                            .requireNonNull(services.getTypeConverter().getHeapLDT(), "heap LDT")
                            .getFieldSymbolForPV(et, services);
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
        for (LocationVariable h : HeapContext.getModifiableHeaps(services, false)) {
            if (hc >= pm.getHeapCount(services)) {
                break;
            }
            heaps.add(h);
        }
        ImmutableList<SLExpression> params = parameters.parameters();
        int i = 0;
        JTerm[] subs = new JTerm[params.size() - pm.getHeapCount(services)
                + pm.getStateCount() * pm.getHeapCount(services) + (pm.isStatic() ? 0 : 1)];
        for (LocationVariable heap : heaps) {
            if (pm.getStateCount() >= 1) {
                subs[i++] = services.getTermBuilder().var(heap);
                if (pm.getStateCount() == 2) {
                    subs[i++] = Objects.requireNonNull(params.head().getTerm(), "no heap term");
                }
            }
            params = params.tail();
        }

        if (!pm.isStatic()) {
            if (!recv.isTerm()) {
                throw manager.excManager.createException("non-static method (" + methodName
                    + ") invocation" + " on Type " + recv.getType());
            }
            subs[i++] = Objects.requireNonNull(recTerm, "no receiver term");
        }

        for (SLExpression slExpression : params) {
            // Remember: parameters.isLisOfTerm() is true!
            final JTerm term = Objects.requireNonNull(slExpression.getTerm(), "no term");
            subs[i] = term.sort() == JavaDLTheory.FORMULA
                    ? services.getTermBuilder().convertToBoolean(term)
                    : term;
            i++;
        }

        if (pm.isVoid()) {
            throw manager.excManager.createException(
                "can not use void " + "method \"" + methodName + "\" in specification expression.");
        }

        return new SLExpression(services.getTermBuilder().tf().createTerm(pm, subs),
            Objects.requireNonNull(pm.getReturnType(), "no return type"));
    }

}
