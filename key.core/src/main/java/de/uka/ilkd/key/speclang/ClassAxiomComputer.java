/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.ast.declaration.ModifierKind;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

/**
 * Computes and caches the class axioms of a {@link KeYJavaType}: the explicitly registered axioms
 * ({@link #addClassAxiom(ClassAxiom)}), the axioms induced by {@link ClassInvariant} declarations
 * ({@code inv}/{@code staticInv}/{@code inv_free}/{@code staticInv_free} definition axioms,
 * {@link PartialInvAxiom}s), {@link QueryAxiom}s for query methods, the axioms derived from model
 * methods ({@link RepresentsAxiom}/{@link ContractAxiom}), the axioms visible from other classes,
 * and (recursively) the axioms of an enclosing class.
 *
 * <p>
 * This is the part of the former {@code SpecificationRepository} that synthesizes derived
 * specification elements. It is owned by the {@link Services} of the environment (shared by
 * {@link Services#copy(boolean)} copies like the specification repository and the proof registry)
 * and no longer part of the specification repository: all inputs ({@link JavaInfo}, registered
 * invariants/axioms, operation contracts) are read from the services / the (still existing)
 * repository when the axioms for a type are computed for the first time and the result is memoized.
 * </p>
 *
 * <p>
 * The memo ({@link #allClassAxiomsCache}) must return <em>the same instances</em> on every call:
 * {@link ClassAxiom} does not implement {@link Object#equals(Object)}/{@link Object#hashCode()},
 * so the default reference check is used and different references would break callers that rely
 * on instance identity (e.g. axiom filtering in proof obligation generation).
 * </p>
 */
public class ClassAxiomComputer {

    protected final Services services;
    protected final TermBuilder tb;

    private final Map<KeYJavaType, ImmutableSet<ClassInvariant>> invs = new LinkedHashMap<>();
    protected final Map<KeYJavaType, ImmutableSet<ClassAxiom>> axioms = new LinkedHashMap<>();

    /**
     * <p>
     * This {@link Map} is used to store the result of {@link #getClassAxioms(KeYJavaType)} to avoid
     * that {@link RepresentsAxiom} and {@link QueryAxiom} are instantiated multiple times.
     * </p>
     * <p>
     * It is strongly required that always the same instances are returned because
     * {@link Object#equals(Object)} and {@link Object#hashCode()} is not implemented in instances
     * of {@link ClassAxiom} and such the default reference check is done which off cause always
     * fails in case of different references.
     * </p>
     */
    private final Map<KeYJavaType, ImmutableSet<ClassAxiom>> allClassAxiomsCache =
        new LinkedHashMap<>();

    public ClassAxiomComputer(Services services) {
        this.services = services;
        this.tb = services.getTermBuilder();
    }

    /**
     * <p>
     * Returns all known class invariants for the passed type.
     * </p>
     * <p>
     * This method is used by Visual DbC and has to be public.
     * </p>
     */
    public ImmutableSet<ClassInvariant> getClassInvariants(KeYJavaType kjt) {
        ImmutableSet<ClassInvariant> result = invs.get(kjt);
        return result == null ? DefaultImmutableSet.nil() : result;
    }

    /**
     * Returns the kjt for the outer class, if the passed kjt is a member class, and null otherwise.
     */
    private KeYJavaType getEnclosingKJT(KeYJavaType kjt) {
        // HACK, this should be easier
        if (kjt.getJavaType() instanceof ClassDeclaration) {

            final String name = kjt.getJavaType().getFullName();

            if (name.contains(".")) {
                final String enclosingName = name.substring(0, name.lastIndexOf('.'));
                return services.getJavaInfo().getTypeByName(enclosingName);
            } else {
                return null;
            }
        } else {
            return null;
        }
    }

    private ImmutableSet<ClassAxiom> getVisibleAxiomsOfOtherClasses(KeYJavaType visibleTo) {
        ImmutableSet<ClassAxiom> result = DefaultImmutableSet.nil();
        for (Map.Entry<KeYJavaType, ImmutableSet<ClassAxiom>> e : axioms.entrySet()) {
            if (e.getKey().equals(visibleTo)) {
                continue;
            }
            for (ClassAxiom ax : e.getValue()) {
                if (JavaInfo.isVisibleTo(ax, visibleTo)) {
                    result = result.add(ax);
                }
            }
        }
        return result;
    }

    private RepresentsAxiom getRepresentsAxiom(KeYJavaType kjt, ClassAxiom ax) {
        if (!(ax instanceof RepresentsAxiom) || axioms.get(kjt) == null) {
            return null;
        }
        RepresentsAxiom result = null;
        for (ClassAxiom ca : axioms.get(kjt)) {
            if (ca instanceof RepresentsAxiom && (ca.getTarget().equals(ax.getTarget()))) {
                assert result == null : "More than one represents clause for " + ax.getTarget();
                result = (RepresentsAxiom) ca;
            }
        }
        return result;
    }

    /**
     * Registers the passed class invariant, and inherits it to all subclasses if it is public or
     * protected.
     */
    public void addClassInvariant(ClassInvariant inv) {
        final KeYJavaType kjt = inv.getKJT();
        invs.put(kjt, getClassInvariants(kjt).add(inv));

        // in any case, create axiom with non-static target
        addClassAxiom(new PartialInvAxiom(inv, false, services));
        // for a static invariant, create also an axiom with a static target
        if (inv.isStatic()) {
            addClassAxiom(new PartialInvAxiom(inv, true, services));
        }
        // inherit non-private, non-static invariants
        if (!inv.isStatic() && ModifierKind.allowsInheritance(inv.getVisibility())) {
            final ImmutableList<KeYJavaType> subs = services.getJavaInfo().getAllSubtypes(kjt);
            for (KeYJavaType sub : subs) {
                ClassInvariant subInv = inv.setKJT(sub);
                invs.put(sub, getClassInvariants(sub).add(subInv));
            }
        }
    }

    /**
     * Registers the passed class invariants.
     */
    public void addClassInvariants(ImmutableSet<ClassInvariant> toAdd) {
        for (ClassInvariant inv : toAdd) {
            addClassInvariant(inv);
        }
    }

    /**
     * Returns all class axioms visible in the passed class, including the axioms induced by
     * invariant declarations.
     */
    public synchronized ImmutableSet<ClassAxiom> getClassAxioms(KeYJavaType selfKjt) {
        ImmutableSet<ClassAxiom> result = allClassAxiomsCache.get(selfKjt);
        if (result == null) {
            // get visible registered axioms of other classes
            result = getVisibleAxiomsOfOtherClasses(selfKjt);
            // add registered axioms of own class
            ImmutableSet<ClassAxiom> ownAxioms = axioms.get(selfKjt);
            if (ownAxioms != null) {
                for (ClassAxiom ax : ownAxioms) {
                    result = result.add(ax);
                }
            }

            final JavaInfo ji = services.getJavaInfo();

            // add invariant axiom for own class and other final classes
            for (KeYJavaType kjt : services.getJavaInfo().getAllKeYJavaTypes()) {
                if (kjt != selfKjt && !ji.isFinal(kjt)) {
                    continue; // only final classes
                }
                if (kjt != selfKjt && JavaInfo.isPrivate(kjt)) {
                    continue; // only non-private classes
                }
                final ImmutableSet<ClassInvariant> myInvs = getClassInvariants(kjt);
                final LocationVariable selfVar = tb.selfVar(kjt, false);

                JTerm invDef = tb.tt();
                JTerm staticInvDef = tb.tt();
                JTerm freeInvDef = tb.tt();
                JTerm freeStaticInvDef = tb.tt();

                for (ClassInvariant inv : myInvs) {
                    if (!inv.isFree()) {
                        invDef = tb.and(invDef, inv.getInv(selfVar, services));
                    } else {
                        freeInvDef = tb.and(freeInvDef, inv.getInv(selfVar, services));
                    }

                    if (inv.isStatic()) {
                        if (!inv.isFree()) {
                            staticInvDef = tb.and(staticInvDef, inv.getInv(null, services));
                        } else {
                            freeStaticInvDef =
                                tb.and(freeStaticInvDef, inv.getInv(selfVar, services));
                        }
                    }
                }

                invDef = tb.tf().createTerm(Equality.EQV, tb.inv(tb.var(selfVar)), invDef);
                staticInvDef = tb.tf().createTerm(Equality.EQV, tb.staticInv(kjt), staticInvDef);
                freeInvDef = tb.tf().createTerm(Equality.EQV,
                    tb.invFree(tb.var(selfVar)), freeInvDef);
                freeStaticInvDef = tb.tf().createTerm(Equality.EQV,
                    tb.staticInvFree(kjt), freeStaticInvDef);

                final IObserverFunction invSymbol = services.getJavaInfo().getInv();
                final IObserverFunction staticInvSymbol = services.getJavaInfo().getStaticInv(kjt);
                final IObserverFunction freeInvSymbol = services.getJavaInfo().getInvFree();
                final IObserverFunction freeStaticInvSymbol = services.getJavaInfo()
                        .getStaticInvFree(kjt);

                final ClassAxiom invRepresentsAxiom =
                    new RepresentsAxiom("Class invariant axiom for " + kjt.getFullName(), invSymbol,
                        kjt, ModifierKind.PRIVATE, null, invDef, selfVar,
                        ImmutableList.nil(), null);
                result = result.add(invRepresentsAxiom);

                final ClassAxiom staticInvRepresentsAxiom = new RepresentsAxiom(
                    "Static class invariant axiom for " + kjt.getFullName(), staticInvSymbol, kjt,
                    ModifierKind.PRIVATE, null, staticInvDef, null, ImmutableList.nil(),
                    null);
                result = result.add(staticInvRepresentsAxiom);

                final ClassAxiom invFreeRepresentsAxiom = new RepresentsAxiom(
                    "Free class invariant axiom for " + kjt.getFullName(), freeInvSymbol, kjt,
                    ModifierKind.PRIVATE, null, freeInvDef, selfVar, ImmutableList.nil(),
                    null);
                result = result.add(invFreeRepresentsAxiom);

                final ClassAxiom staticFreeInvRepresentsAxiom = new RepresentsAxiom(
                    "Free static class invariant axiom for " + kjt.getFullName(),
                    freeStaticInvSymbol, kjt, ModifierKind.PRIVATE, null, freeStaticInvDef,
                    null,
                    ImmutableList.nil(), null);
                result = result.add(staticFreeInvRepresentsAxiom);

            }
            // add query axioms for own class
            for (IProgramMethod pm : services.getJavaInfo().getAllProgramMethods(selfKjt)) {
                if (!pm.isVoid() && !pm.isConstructor() && !pm.isImplicit() && !pm.isModel()) {
                    pm = services.getJavaInfo().getToplevelPM(selfKjt, pm);

                    var sb = new StringBuilder();
                    for (KeYJavaType pd : pm.getParamTypes()) {
                        sb.append(pd.getJavaType().getFullName());
                        sb.append("_");
                    }

                    final ClassAxiom queryAxiom = new QueryAxiom("Query axiom for " + pm.getName()
                        + "_" + sb + " in " + selfKjt.getFullName(), pm, selfKjt);
                    result = result.add(queryAxiom);
                }
            }

            // add model method axioms of all kinds
            result = result.union(getModelMethodAxioms());
            // add axioms for enclosing class, if applicable
            final KeYJavaType enclosingKJT = getEnclosingKJT(selfKjt);
            if (enclosingKJT != null) {
                result = result.union(getClassAxioms(enclosingKJT));
            }
            allClassAxiomsCache.put(selfKjt, result);
        }
        return result;
    }

    private ImmutableSet<ClassAxiom> getModelMethodAxioms() {
        ImmutableSet<ClassAxiom> result = DefaultImmutableSet.nil();
        for (KeYJavaType kjt : services.getJavaInfo().getAllKeYJavaTypes()) {
            for (IProgramMethod pm : services.getJavaInfo().getAllProgramMethods(kjt)) {
                final LocationVariable selfVar = pm.isStatic() ? null : tb.selfVar(kjt, false);
                if (!pm.isVoid() && pm.isModel()) {
                    pm = services.getJavaInfo().getToplevelPM(kjt, pm);
                    ImmutableList<LocationVariable> paramVars = tb.paramVars(pm, false);
                    Map<LocationVariable, LocationVariable> atPreVars = new LinkedHashMap<>();
                    List<LocationVariable> heaps = HeapContext.getModifiableHeaps(services, false);
                    for (LocationVariable heap : heaps) {
                        atPreVars.put(heap,
                            tb.atPreVar(heap.name().toString(), heap.sort(), false));
                    }
                    LocationVariable resultVar = tb.resultVar(pm, false);

                    // This assumes there is one operation contract for each
                    // model pm per class
                    // We need to construct an inheritance chain of contracts
                    // starting at the bottom
                    ImmutableList<FunctionalOperationContract> lookupContracts =
                        ImmutableList.nil();
                    ImmutableSet<FunctionalOperationContract> cs =
                        getOperationContracts(kjt, pm);
                    List<KeYJavaType> superTypes =
                        services.getJavaInfo().getAllSupertypes(kjt);
                    for (KeYJavaType superType : superTypes) {
                        for (FunctionalOperationContract fop : cs) {
                            if (fop.getSpecifiedIn().equals(superType)) {
                                lookupContracts = lookupContracts.append(fop);
                            }
                        }
                    }
                    for (FunctionalOperationContract fop : lookupContracts) {
                        JTerm representsFromContract = fop.getRepresentsAxiom(heaps.get(0), selfVar,
                            paramVars, tb.resultVar(pm, false), atPreVars, services);
                        JTerm preContract =
                            fop.getPre(heaps, selfVar, paramVars, atPreVars, services);
                        if (preContract == null) {
                            preContract = tb.tt();
                        }
                        if (representsFromContract != null) {
                            // TODO Wojtek: I do not understand the visibility
                            // issues of model fields/methods.
                            // Modifier visibility = pm.isPrivate() ?
                            // new Private() :
                            // (pm.isProtected() ? new Protected() :
                            // (pm.isPublic() ? new Public() : null));
                            final ClassAxiom modelMethodRepresentsAxiom =
                                new RepresentsAxiom(
                                    "Definition axiom for " + pm.getName() + " in "
                                        + kjt.getFullName(),
                                    pm, kjt, ModifierKind.PRIVATE, preContract,
                                    representsFromContract,
                                    selfVar, paramVars, atPreVars);
                            result = result.add(modelMethodRepresentsAxiom);
                            break;
                        }
                    }
                    for (FunctionalOperationContract fop : getOperationContracts(kjt, pm)) {
                        if (!fop.getSpecifiedIn().equals(kjt)) {
                            continue;
                        }
                        JTerm preFromContract =
                            fop.getPre(heaps, selfVar, paramVars, atPreVars, services);
                        JTerm freePreFromContract =
                            fop.getFreePre(heaps, selfVar, paramVars, atPreVars, services);
                        JTerm postFromContract = fop.getPost(heaps, selfVar, paramVars, resultVar,
                            null, atPreVars, services);
                        JTerm freePostFromContract = fop.getFreePost(heaps, selfVar, paramVars,
                            resultVar, null, atPreVars, services);
                        if (preFromContract != null
                                && ((postFromContract != null && postFromContract != tb.tt())
                                        || (freePostFromContract != null
                                                && freePostFromContract != tb.tt()))) {
                            JTerm mbyFromContract =
                                fop.hasMby() ? fop.getMby(selfVar, paramVars, services) : null;
                            final ClassAxiom modelMethodContractAxiom = new ContractAxiom(
                                "Contract axiom for " + pm.getName() + " in " + kjt.getFullName(),
                                pm,
                                kjt, ModifierKind.PRIVATE, preFromContract,
                                freePreFromContract,
                                postFromContract, freePostFromContract, mbyFromContract, atPreVars,
                                selfVar, resultVar, paramVars);
                            result = result.add(modelMethodContractAxiom);
                        }
                    }
                }
            }
        }
        return result;
    }

    /**
     * Returns the class axioms declared in (registered for) the given type. This is the group among
     * which a {@link de.uka.ilkd.key.speclang.ClassAxiomImpl}'s taclet name must be unique; order
     * is
     * not significant.
     *
     * @param kjt the type
     * @return the axioms registered for {@code kjt}, or the empty set if none
     */
    public synchronized ImmutableSet<ClassAxiom> getClassAxiomsForType(KeYJavaType kjt) {
        final ImmutableSet<ClassAxiom> own = axioms.get(kjt);
        return own == null ? DefaultImmutableSet.nil() : own;
    }

    /**
     * Registers the passed class axiom.
     */
    public void addClassAxiom(ClassAxiom ax) {
        KeYJavaType kjt = ax.getKJT();
        ImmutableSet<ClassAxiom> currentAxioms = axioms.get(kjt);
        if (currentAxioms == null) {
            currentAxioms = DefaultImmutableSet.nil();
        }
        if (ax instanceof RepresentsAxiom) {
            // there may only be one conjoined represents axiom per model field
            RepresentsAxiom oldRep = getRepresentsAxiom(kjt, ax);
            if (oldRep != null) {
                final RepresentsAxiom newRep = oldRep.conjoin((RepresentsAxiom) ax, tb);
                axioms.put(kjt, currentAxioms.remove(oldRep).add(newRep));
            } else {
                axioms.put(kjt, currentAxioms.add(ax));
            }
            // inherit represents clauses to subclasses and conjoin together
            if (ModifierKind.allowsInheritance(ax.getVisibility())) {
                final ImmutableList<KeYJavaType> subs = services.getJavaInfo().getAllSubtypes(kjt);
                for (KeYJavaType sub : subs) {
                    RepresentsAxiom subAx = ((RepresentsAxiom) ax).setKJT(sub);
                    currentAxioms = axioms.get(sub);
                    if (currentAxioms == null) {
                        currentAxioms = DefaultImmutableSet.nil();
                    }
                    oldRep = getRepresentsAxiom(sub, subAx);
                    if (oldRep == null) {
                        axioms.put(sub, currentAxioms.add(subAx));
                    } else {
                        final RepresentsAxiom newSubRep = oldRep.conjoin(subAx, tb);
                        axioms.put(sub, currentAxioms.remove(oldRep).add(newSubRep));
                    }
                }
            }
        } else {
            axioms.put(kjt, currentAxioms.add(ax));
        }
    }

    /**
     * Registers the passed class axioms.
     */
    public void addClassAxioms(ImmutableSet<ClassAxiom> toAdd) {
        for (ClassAxiom ax : toAdd) {
            addClassAxiom(ax);
        }
    }

    /**
     * Applies the specified operator to every invariant and class axiom of this computer
     * (including the memoized computed axiom sets).
     *
     * @param op an operator.
     * @param services services.
     * @see SpecificationElement#map(UnaryOperator, Services)
     */
    public synchronized void map(UnaryOperator<JTerm> op, Services services) {
        mapValueSets(invs, op, services);
        mapValueSets(axioms, op, services);
        mapValueSets(allClassAxiomsCache, op, services);
    }

    /**
     * Applies the specified operator to every specification element in the passed map.
     *
     * @param map a map.
     * @param op an operator.
     * @param services services.
     */
    @SuppressWarnings("unchecked")
    protected <K, V extends SpecificationElement> void mapValueSets(Map<K, ImmutableSet<V>> map,
            UnaryOperator<JTerm> op, Services services) {
        for (Entry<K, ImmutableSet<V>> entry : map.entrySet()) {
            final K key = entry.getKey();
            final ImmutableSet<V> oldSet = entry.getValue();
            ImmutableSet<V> newSet = DefaultImmutableSet.nil();

            for (V oldSpec : oldSet) {
                newSet = newSet.add((V) oldSpec.map(op, services));
            }

            map.put(key, newSet);
        }
    }

    /**
     * Returns the operation contracts registered for the given model method. <em>Temporary
     * bridge:</em> the contract registry still lives in the specification repository (it moves in a
     * later Phase-4 slice); once it does, this lookup switches to the contract registry.
     *
     * @param kjt the type.
     * @param pm the model method.
     * @return the registered operation contracts for {@code pm} in {@code kjt}.
     */
    private ImmutableSet<FunctionalOperationContract> getOperationContracts(KeYJavaType kjt,
            IProgramMethod pm) {
        return services.getSpecificationRepository().getOperationContracts(kjt, pm);
    }
}
