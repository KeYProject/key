/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

/**
 * A class axiom corresponding to a JML* represents clause.
 */
public final class RepresentsAxiom extends ClassAxiom {

    private final String name;
    private final IObserverFunction target;
    private final KeYJavaType kjt;
    private final VisibilityModifier visibility;
    private final Term originalPre;
    private final Term originalRep;
    private final ProgramVariable originalSelfVar;
    /**
     * The mapping of the pre-heaps.
     */
    private final Map<LocationVariable, ProgramVariable> atPreVars;
    private final ImmutableList<ProgramVariable> originalParamVars;

    public RepresentsAxiom(String name, IObserverFunction target, KeYJavaType kjt,
            VisibilityModifier visibility, Term pre, Term rep, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ProgramVariable> atPreVars) {
        this(name, null, target, kjt, visibility, pre, rep, selfVar, paramVars, atPreVars);
    }

    public RepresentsAxiom(String name, String displayName, IObserverFunction target,
            KeYJavaType kjt, VisibilityModifier visibility, Term pre, Term rep,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ProgramVariable> atPreVars) {
        assert name != null;
        assert kjt != null;
        assert target != null;
        assert rep.sort() == Sort.FORMULA;
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
    public SpecificationElement map(UnaryOperator<Term> op, Services services) {
        return new RepresentsAxiom(name, displayName, target, kjt, visibility,
            op.apply(originalPre), op.apply(originalRep), originalSelfVar, originalParamVars,
            atPreVars);
    }

    @Override
    public boolean equals(Object o) {
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

    public Term getAxiom(ParsableVariable heapVar, ParsableVariable selfVar, Services services) {
        assert heapVar != null;
        assert (selfVar == null) == target.isStatic();
        final Map<ProgramVariable, ParsableVariable> map =
            new LinkedHashMap<>();
        map.put(services.getTypeConverter().getHeapLDT().getHeap(), heapVar);
        if (selfVar != null) {
            map.put(originalSelfVar, selfVar);
        }
        final OpReplacer or = new OpReplacer(map, services.getTermFactory(), services.getProof());
        return or.replace(originalRep);
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
    public VisibilityModifier getVisibility() {
        return visibility;
    }

    @Override
    public ImmutableSet<Taclet> getTaclets(ImmutableSet<Pair<Sort, IObserverFunction>> toLimit,
            final Services services) {
        List<LocationVariable> heaps = new ArrayList<>();
        int hc = 0;
        for (LocationVariable h : HeapContext.getModHeaps(services, false)) {
            if (hc >= target.getHeapCount(services)) {
                break;
            }
            heaps.add(h);
        }
        ProgramVariable self = (!target.isStatic() ? originalSelfVar : null);

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
                        + "this should not have occured.");
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
        VisibilityModifier minVisibility = visibility == null
                ? (VisibilityModifier.isPrivate(ax.visibility) ? ax.visibility : null)
                : (visibility.compareTo(ax.visibility) >= 0 ? visibility : ax.visibility);
        Term newRep = tb.and(originalRep, ax.originalRep);
        Term newPre = null;
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
