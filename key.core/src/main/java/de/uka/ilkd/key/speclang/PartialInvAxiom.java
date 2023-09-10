/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.LinkedList;
import java.util.List;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

/**
 * A class axiom which is essentially of the form "o.<inv> -> phi": it demands that the invariants
 * of the objects of a particular class imply a particular formula. These axioms are logically
 * weaker than the full definitions of <inv> expressed as RepresentsAxioms, but they may have higher
 * visibility, making them available in proofs where the corresponding full definition is not.
 */
public final class PartialInvAxiom extends ClassAxiom {

    /**
     * The partial invariant from which the axiom is derived.
     */
    private final ClassInvariant inv;
    /**
     * The partial invariant function symbol.
     */
    private final IObserverFunction target;
    /**
     * Whether the axiom matches static invariants (i.e., &lt;$inv&gt;) or instance invariants
     * (i.e., &lt;inv&gt;).
     */
    private final boolean isStatic;

    /**
     * Creates a new class axiom.
     *
     * @param inv (partial) invariant from which the axiom is derived
     * @param isStatic whether the axiom should match static invariants (i.e., &lt;$inv&gt;) or
     *        instance invariants (i.e., &lt;inv&gt;)
     * @param services
     */
    public PartialInvAxiom(ClassInvariant inv, boolean isStatic, Services services) {
        assert inv != null;
        this.inv = inv;
        assert !isStatic || inv.isStatic();
        this.isStatic = isStatic;
        this.target = isStatic ? services.getJavaInfo().getStaticInv(inv.getKJT())
                : services.getJavaInfo().getInv();
        assert target != null;
    }

    public PartialInvAxiom(ClassInvariant inv, String displayName, Services services) {
        this(inv, false, services);
        this.displayName = displayName;
    }

    @Override
    public SpecificationElement map(UnaryOperator<Term> op, Services services) {
        PartialInvAxiom result = new PartialInvAxiom(inv.map(op, services), isStatic, services);
        result.displayName = displayName;
        return result;
    }


    @Override
    public boolean equals(Object o) {
        if (o == null || this.getClass() != o.getClass()) {
            return false;
        }
        final PartialInvAxiom other = (PartialInvAxiom) o;

        if (!target.equals(other.target)) {
            return false;
        }
        return inv.equals(other.inv);
    }

    @Override
    public int hashCode() {
        return 17 * (inv.hashCode() + 17 * target.hashCode());
    }

    @Override
    public String getName() {
        return inv.getName();
    }


    @Override
    public IObserverFunction getTarget() {
        return target;
    }


    @Override
    public KeYJavaType getKJT() {
        return inv.getKJT();
    }


    @Override
    public VisibilityModifier getVisibility() {
        return inv.getVisibility();
    }


    @Override
    public ImmutableSet<Taclet> getTaclets(ImmutableSet<Pair<Sort, IObserverFunction>> toLimit,
            Services services) {
        ImmutableSet<Taclet> result = DefaultImmutableSet.nil();

        for (int i = 0; i < 2; i++) {
            // i==0 normal and i==1 EQ version
            TacletGenerator TG = TacletGenerator.getInstance();
            final Name name = MiscTools.toValidTacletName("Partial inv axiom for "
                + (target.isStatic() ? "static " : "") + inv.getName() + (i == 0 ? "" : " EQ"));

            // create schema variables
            final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
            final List<SchemaVariable> heapSVs = new LinkedList<>();
            for (int j = 0; j < HeapContext.getModHeaps(services, false).size(); j++) {
                heapSVs.add(SchemaVariableFactory.createTermSV(new Name("h" + j),
                    heapLDT.targetSort(), false, false));
            }
            final SchemaVariable selfSV = target.isStatic() ? null
                    : SchemaVariableFactory.createTermSV(new Name("self"), inv.getKJT().getSort());
            final SchemaVariable eqSV = target.isStatic() ? null
                    : SchemaVariableFactory.createTermSV(new Name("EQ"),
                        services.getJavaInfo().objectSort());

            ImmutableSet<Taclet> taclets = TG.generatePartialInvTaclet(name, heapSVs, selfSV, eqSV,
                inv.getInv(selfSV, services), inv.getKJT(), toLimit, target.isStatic(),
                inv.isFree(), i == 1, services);
            result = result.union(taclets);

            // EQ taclet (with i==1) only for non-static invariants
            if (target.isStatic()) {
                break;
            }
        }

        // return
        return result;
    }


    @Override
    public ImmutableSet<Pair<Sort, IObserverFunction>> getUsedObservers(Services services) {
        final ProgramVariable dummySelfVar = services.getTermBuilder().selfVar(inv.getKJT(), false);
        return MiscTools.collectObservers(inv.getInv(dummySelfVar, services));
    }

    @Override
    public String toString() {
        return inv.toString();
    }

    public ClassInvariant getInv() {
        return inv;
    }
}
