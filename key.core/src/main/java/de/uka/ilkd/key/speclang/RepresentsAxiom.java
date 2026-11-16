/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.declaration.ModifierKind;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * A class axiom corresponding to a JML* represents clause.
 */
@NullMarked
public final class RepresentsAxiom extends ClassAxiom {

    private final String name;
    private final IObserverFunction target;
    private final KeYJavaType kjt;
    private final @Nullable ModifierKind visibility;
    private final @Nullable JTerm originalPre;
    private final JTerm originalRep;
    private final @Nullable LocationVariable originalSelfVar;
    /**
     * The mapping of the pre-heaps.
     */
    private final Map<LocationVariable, LocationVariable> atPreVars;
    private final ImmutableList<LocationVariable> originalParamVars;

    public RepresentsAxiom(String name, IObserverFunction target, KeYJavaType kjt,
            @Nullable ModifierKind visibility, @Nullable JTerm pre, JTerm rep,
            @Nullable LocationVariable selfVar,
            ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars) {
        this(name, null, target, kjt, visibility, pre, rep, selfVar, paramVars, atPreVars);
    }

    public RepresentsAxiom(String name, @Nullable String displayName, IObserverFunction target,
            KeYJavaType kjt, @Nullable ModifierKind visibility, @Nullable JTerm pre, JTerm rep,
            @Nullable LocationVariable selfVar, ImmutableList<LocationVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars) {
        assert name != null;
        assert kjt != null;
        assert target != null;
        assert rep.sort() == JavaDLTheory.FORMULA;
        assert (selfVar == null) == target.isStatic();
        this.name = name;
        this.target = target;
        this.kjt = kjt;
        this.visibility = visibility;
        this.originalPre = pre;
        this.originalRep = rep;
        this.originalSelfVar = selfVar;
        this.originalParamVars = paramVars;
        this.atPreVars = atPreVars;
        this.displayName = displayName;
    }

    @Override
    public SpecificationElement map(UnaryOperator<JTerm> op, Services services) {
        return new RepresentsAxiom(name, displayName, target, kjt, visibility,
            originalPre != null ? op.apply(originalPre) : null, op.apply(originalRep),
            originalSelfVar, originalParamVars, atPreVars);
    }

    @Override
    public boolean equals(@Nullable Object o) {
        if (o == null || o.getClass() != getClass()) {
            return false;
        }
        RepresentsAxiom other = (RepresentsAxiom) o;
        if (!name.equals(other.name)) {
            return false;
        }
        if (target != other.target) {
            return false;
        }
        return kjt.equals(other.kjt);
    }

    @Override
    public int hashCode() {
        return name.hashCode() + 13 * target.hashCode();
    }

    private boolean isFunctional(Services services) {
        return originalRep.op() instanceof Equality && originalRep.sub(0).op() == target
                && (target.isStatic() || originalRep.sub(0)
                        .sub(target.getStateCount() * target.getHeapCount(services)).op()
                        .equals(originalSelfVar));
    }

    /**
     * Builds the axiom term in which {@code heapVar} replaces the heap method and {@code selfVar}
     * replaces the self variable, if any.
     * <p>
     * The key {@link #originalSelfVar} is nullable by declaration, but the constructor invariant
     * {@code (selfVar == null) == target.isStatic()} guarantees that field is non-null exactly
     * when the method's {@code selfVar} parameter is non-null. The checker cannot derive this
     * link, so the {@code Map.put} of the key is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    public JTerm getAxiom(JAbstractSortedOperator heapVar,
            @Nullable JAbstractSortedOperator selfVar,
            Services services) {
        assert heapVar != null;
        // assert (selfVar == null) == target.isStatic();
        final HeapLDT heapLDT =
            Objects.requireNonNull(services.getTypeConverter().getHeapLDT(), "heap LDT");
        final Map<ProgramVariable, JAbstractSortedOperator> map = new LinkedHashMap<>();
        map.put(heapLDT.getHeap(), heapVar);
        if (selfVar != null) {
            map.put(originalSelfVar, selfVar);
        }
        final OpReplacer or = new OpReplacer(map, services.getTermFactory(), services.getProof());
        return Objects.requireNonNull(or.replace(originalRep), "no replacement for term");
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public IObserverFunction getTarget() {
        return target;
    }

    @Override
    public KeYJavaType getKJT() {
        return kjt;
    }

    @Override
    public @Nullable ModifierKind getVisibility() {
        return visibility;
    }

    @Override
    public ImmutableSet<Taclet> getTaclets(ImmutableSet<Pair<Sort, IObserverFunction>> toLimit,
            final Services services) {
        List<LocationVariable> heaps = new ArrayList<>();
        int hc = 0;
        for (LocationVariable h : HeapContext.getModifiableHeaps(services, false)) {
            if (hc >= target.getHeapCount(services)) {
                break;
            }
            heaps.add(h);
        }
        LocationVariable self = (!target.isStatic() ? originalSelfVar : null);

        Name tacletName = MiscTools.toValidTacletName(name);
        TacletGenerator tg = TacletGenerator.getInstance();
        if (isFunctional(services)) {
            ImmutableSet<Taclet> res = DefaultImmutableSet.nil();
            res = res.union(
                tg.generateFunctionalRepresentsTaclets(tacletName, originalPre, originalRep, kjt,
                    target, heaps, self, originalParamVars, atPreVars, toLimit, true, services));
            res = res.union(
                tg.generateFunctionalRepresentsTaclets(tacletName, originalPre, originalRep, kjt,
                    target, heaps, self, originalParamVars, atPreVars, toLimit, false, services));
            return res;
        } else {
            if (originalPre != null) {
                // FIXME weigl: this was a runtime exception, I am not sure why.
                // I need a little bit help, why this is triggerd for my JML thing.
                throw new IllegalStateException(
                    "Only functional represents for model methods is currently supported,"
                        + "this should not have occurred. Name:" + name);
            }
            Taclet tacletWithShowSatisfiability =
                tg.generateRelationalRepresentsTaclet(tacletName, originalRep, kjt, target, heaps,
                    self, originalParamVars, atPreVars, true, services);
            Taclet tacletWithTreatAsAxiom =
                tg.generateRelationalRepresentsTaclet(tacletName, originalRep, kjt, target, heaps,
                    self, originalParamVars, atPreVars, false, services);
            return DefaultImmutableSet.<Taclet>nil().add(tacletWithShowSatisfiability)
                    .add(tacletWithTreatAsAxiom);
        }
    }

    @Override
    public ImmutableSet<Pair<Sort, IObserverFunction>> getUsedObservers(Services services) {
        if (!isFunctional(services)) {
            return DefaultImmutableSet.nil();
        } else {
            return MiscTools.collectObservers(originalRep.sub(1));
        }
    }

    @Override
    public String toString() {
        return originalRep.toString();
    }

    public RepresentsAxiom setKJT(KeYJavaType newKjt) {
        String newName =
            "JML represents clause for " + target + " (subclass " + newKjt.getName() + ")";
        return new RepresentsAxiom(newName, displayName, target, newKjt, visibility, originalPre,
            originalRep, originalSelfVar, originalParamVars, atPreVars);
    }

    /**
     * <p>
     * Conjoins two represents clauses with minimum visibility. An exception is thrown if the
     * targets or types are different.
     * </p>
     *
     * <p>
     * <b>Known issue</b>: public clauses in subclasses are hidden by protected clauses in
     * superclasses; this only applies to observers outside the package of the subclass (whenever
     * package-privacy is implemented).
     * </p>
     *
     * @param ax some represents clause.
     * @param tb a term builder.
     * @return a conjunction of this clause and {@code ax}.
     */
    public RepresentsAxiom conjoin(RepresentsAxiom ax, TermBuilder tb) {
        if (!target.equals(ax.target) || !kjt.equals(ax.kjt)) {
            throw new RuntimeException("Tried to conjoin incompatible represents axioms.");
        }
        ModifierKind minVisibility = ModifierKind.moreRestrictive(visibility, ax.visibility);
        JTerm newRep = tb.and(originalRep, ax.originalRep);
        JTerm newPre;
        if (originalPre == null) {
            newPre = ax.originalPre;
        } else if (ax.originalPre == null) {
            newPre = originalPre;
        } else {
            newPre = tb.and(originalPre, ax.originalPre);
        }
        return new RepresentsAxiom(name, displayName, target, kjt, minVisibility, newPre, newRep,
            originalSelfVar, originalParamVars, atPreVars);
    }

    public OriginalVariables getOrigVars() {
        return new OriginalVariables(originalSelfVar, null, null, atPreVars, originalParamVars);
    }
}
