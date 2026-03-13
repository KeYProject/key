/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;


public final class DropEffectlessStoresCondition implements VariableCondition {
    private final TermSV h;
    private final TermSV o;
    private final TermSV f;
    private final TermSV x;
    private final TermSV result;

    public DropEffectlessStoresCondition(TermSV h, TermSV o, TermSV f, TermSV x, TermSV result) {
        this.h = h;
        this.o = o;
        this.f = f;
        this.x = x;
        this.result = result;
    }


    private static JTerm dropEffectlessStoresHelper(JTerm heapTerm, TermServices services,
            ImmutableSet<Pair<JTerm, JTerm>> overwrittenLocs, Function store) {
        if (heapTerm.op() == store) {
            final JTerm subHeapTerm = heapTerm.sub(0);
            final JTerm objTerm = heapTerm.sub(1);
            final JTerm fieldTerm = heapTerm.sub(2);
            final JTerm valueTerm = heapTerm.sub(3);
            final Pair<JTerm, JTerm> loc = new Pair<>(objTerm, fieldTerm);
            final JTerm newSubHeapTerm =
                dropEffectlessStoresHelper(subHeapTerm, services, overwrittenLocs.add(loc), store);
            if (overwrittenLocs.contains(loc)) {
                return newSubHeapTerm == null ? subHeapTerm : newSubHeapTerm;
            } else {
                return newSubHeapTerm == null ? null
                        : services.getTermBuilder().store(newSubHeapTerm, objTerm, fieldTerm,
                            valueTerm);
            }
        } else {
            return null;
        }
    }


    private static JTerm dropEffectlessStores(JTerm t, Services services) {
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        assert t.sort() == heapLDT.targetSort();
        return dropEffectlessStoresHelper(t, services, DefaultImmutableSet.nil(),
            heapLDT.getStore());
    }


    @Override
    public MatchResultInfo check(SchemaVariable var, SyntaxElement instCandidate,
            MatchResultInfo mc,
            LogicServices p_services) {
        final Services services = (Services) p_services;
        var svInst = (SVInstantiations) mc.getInstantiations();
        JTerm hInst = svInst.getInstantiation(h);
        JTerm oInst = svInst.getInstantiation(o);
        JTerm fInst = svInst.getInstantiation(f);
        JTerm xInst = svInst.getInstantiation(x);
        JTerm resultInst = svInst.getInstantiation(result);
        if (hInst == null || oInst == null || fInst == null || xInst == null) {
            return mc;
        }

        final JTerm properResultInst = dropEffectlessStores(
            services.getTermBuilder().store(hInst, oInst, fInst, xInst), services);
        if (properResultInst == null) {
            return null;
        } else if (resultInst == null) {
            svInst = svInst.add(result, properResultInst, services);
            return mc.setInstantiations(svInst);
        } else if (resultInst.equals(properResultInst)) {
            return mc;
        } else {
            return null;
        }
    }


    @Override
    public String toString() {
        return "\\dropEffectlessStores(" + h + ", " + o + ", " + f + ", " + x + ", " + result + ")";
    }
}
