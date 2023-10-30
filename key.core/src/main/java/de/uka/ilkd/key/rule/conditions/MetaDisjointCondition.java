/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;


public final class MetaDisjointCondition extends VariableConditionAdapter {

    private final TermSV var1;
    private final TermSV var2;


    public MetaDisjointCondition(TermSV s1, TermSV s2) {
        this.var1 = s1;
        this.var2 = s2;
    }


    private static boolean clearlyDisjoint(Term t1, Term t2, Services services) {
        final LocSetLDT setLDT = services.getTypeConverter().getLocSetLDT();
        if (t1.op() instanceof Function && ((Function) t1.op()).isUnique()
                && t2.op() instanceof Function && ((Function) t2.op()).isUnique()
                && !t1.equals(t2)) {
            return true;
        } else if (t1.sort().equals(setLDT.targetSort()) && t2.sort().equals(setLDT.targetSort())) {
            final ImmutableSet<Term> t1set = services.getTermBuilder().unionToSet(t1);
            final ImmutableSet<Term> t2set = services.getTermBuilder().unionToSet(t2);

            ImmutableSet<Operator> t1Ops = DefaultImmutableSet.nil();
            ImmutableSet<Operator> t2Ops = DefaultImmutableSet.nil();
            for (Term t : t1set) {
                if (t.op().equals(setLDT.getSingleton()) && t.sub(0).op() instanceof Function
                        && ((Function) t.sub(0).op()).isUnique()) {
                    t1Ops = t1Ops.add(t.op());
                } else if (t.op().equals(setLDT.getEmpty())) {
                } else {
                    return false;
                }
            }
            for (Term t : t2set) {
                if (t.op().equals(setLDT.getSingleton()) && t.sub(0).op() instanceof Function
                        && ((Function) t.sub(0).op()).isUnique()) {
                    t2Ops = t2Ops.add(t.op());
                } else if (t.op().equals(setLDT.getEmpty())) {
                } else {
                    return false;
                }
            }

            return t1Ops.intersect(t2Ops).isEmpty();
        } else {
            return false;
        }
    }


    @Override
    public boolean check(SchemaVariable var, SVSubstitute subst, SVInstantiations svInst,
            Services services) {
        final Term s1Inst = (Term) svInst.getInstantiation(var1);
        final Term s2Inst = (Term) svInst.getInstantiation(var2);
        if (s1Inst == null || s2Inst == null) {
            return true;
        } else {
            return clearlyDisjoint(s1Inst, s2Inst, services);
        }
    }


    @Override
    public String toString() {
        return ("\\metaDisjoint " + var1 + ", " + var2);
    }
}
