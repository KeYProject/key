/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;


public final class ContractAxiom extends ClassAxiom {

    private final String name;
    private final IObserverFunction target;
    private final KeYJavaType kjt;
    private final VisibilityModifier visibility;
    private final Term originalPre;
    private final Term originalFreePre;
    private final Term originalPost;
    private final Term originalFreePost;
    private final Term originalMby;
    private final ProgramVariable originalSelfVar;
    private final ProgramVariable originalResultVar;
    private final ImmutableList<ProgramVariable> originalParamVars;
    private final Map<LocationVariable, ProgramVariable> atPreVars;

    public ContractAxiom(String name, IObserverFunction target, KeYJavaType kjt,
            VisibilityModifier visibility, Term pre, Term freePre, Term post, Term freePost,
            Term mby, Map<LocationVariable, ProgramVariable> atPreVars, ProgramVariable selfVar,
            ProgramVariable resultVar, ImmutableList<ProgramVariable> paramVars) {
        this(name, null, target, kjt, visibility, pre, freePre, post, freePost, mby, atPreVars,
            selfVar, resultVar, paramVars);
    }

    public ContractAxiom(String name, String displayName, IObserverFunction target, KeYJavaType kjt,
            VisibilityModifier visibility, Term originalPre, Term originalFreePre,
            Term originalPost, Term originalFreePost, Term originalMby,
            Map<LocationVariable, ProgramVariable> atPreVars, ProgramVariable selfVar,
            ProgramVariable resultVar, ImmutableList<ProgramVariable> paramVars) {

        assert name != null;
        assert kjt != null;
        assert target != null;
        assert originalPre.sort() == Sort.FORMULA;
        assert originalPost.sort() == Sort.FORMULA;
        assert (selfVar == null) == target.isStatic();
        this.name = name;
        this.target = target;
        this.kjt = kjt;
        this.visibility = visibility;
        this.originalPre = originalPre;
        this.originalFreePre = originalFreePre;
        this.originalPost = originalPost;
        this.originalFreePost = originalFreePost;
        this.originalMby = originalMby;
        this.originalSelfVar = selfVar;
        this.originalResultVar = resultVar;
        this.originalParamVars = paramVars;
        this.atPreVars = atPreVars;
        this.displayName = displayName;
    }

    @Override
    public ContractAxiom map(UnaryOperator<Term> op, Services services) {
        return new ContractAxiom(name, displayName, target, kjt, visibility, op.apply(originalPre),
            op.apply(originalFreePre), op.apply(originalPost), op.apply(originalFreePost),
            op.apply(originalMby), atPreVars, originalSelfVar, originalResultVar,
            originalParamVars);
    }

    @Override
    public ImmutableSet<Taclet> getTaclets(ImmutableSet<Pair<Sort, IObserverFunction>> toLimit,
            Services services) {

        final boolean satisfiabilityGuard = true; // XXX
        List<LocationVariable> heaps = HeapContext.getModHeaps(services, false);
        ProgramVariable self = (!target.isStatic() ? originalSelfVar : null);

        Name tacletName = MiscTools.toValidTacletName(name);
        TacletGenerator TG = TacletGenerator.getInstance();
        return TG.generateContractAxiomTaclets(tacletName, originalPre, originalFreePre,
            originalPost, originalFreePost, originalMby, kjt, target, heaps, self,
            originalResultVar, atPreVars, originalParamVars, toLimit, satisfiabilityGuard,
            services);
    }

    @Override
    public boolean equals(Object o) {
        if (o == null || this.getClass() != o.getClass()) {
            return false;
        }
        final ContractAxiom other = (ContractAxiom) o;

        if (!name.equals(other.name)) {
            return false;
        }
        if (!target.equals(other.target)) {
            return false;
        }
        return kjt.equals(other.kjt);
    }

    @Override
    public int hashCode() {
        return 17 * (name.hashCode() + 17 * target.hashCode());
    }

    @Override
    public ImmutableSet<Pair<Sort, IObserverFunction>> getUsedObservers(Services services) {
        return MiscTools.collectObservers(originalPre)
                .union(MiscTools.collectObservers(originalPost))
                .union(MiscTools.collectObservers(originalFreePre))
                .union(MiscTools.collectObservers(originalFreePost));
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

}
