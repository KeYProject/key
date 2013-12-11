// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;


public final class ContractAxiom extends ClassAxiom {

    private final String name;
    private final IObserverFunction target;
    private final KeYJavaType kjt;
    private final VisibilityModifier visibility;
    private final Term originalPre;
    private final Term originalPost;
    private final Term originalMby;
    private final ProgramVariable originalSelfVar;
    private final ProgramVariable originalResultVar;
    private final ImmutableList<ProgramVariable> originalParamVars;
    private final Map<LocationVariable,ProgramVariable> atPreVars;

    public ContractAxiom(String name,
                         IObserverFunction target,
                         KeYJavaType kjt,
                         VisibilityModifier visibility,
                         Term pre,
                         Term post,
                         Term mby,
                         Map<LocationVariable,ProgramVariable> atPreVars,
                         ProgramVariable selfVar,
                         ProgramVariable resultVar,
                         ImmutableList<ProgramVariable> paramVars) {
        this(name,null,target,kjt,visibility,pre,post,mby,atPreVars,selfVar,resultVar,paramVars);
    }

    public ContractAxiom(String name,
            String displayName,
            IObserverFunction target,
                KeYJavaType kjt,
                VisibilityModifier visibility,
                Term originalPre,
                Term originalPost,
                Term originalMby,
                Map<LocationVariable,ProgramVariable> atPreVars,
                ProgramVariable selfVar, ProgramVariable resultVar, ImmutableList<ProgramVariable> paramVars) {

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
        this.originalPost = originalPost;
        this.originalMby = originalMby;
        this.originalSelfVar = selfVar;
        this.originalResultVar = resultVar;
        this.originalParamVars = paramVars;
        this.atPreVars = atPreVars;
        this.displayName = displayName;
    }

    @Override
    public ImmutableSet<Taclet> getTaclets(ImmutableSet<Pair<Sort, IObserverFunction>> toLimit, Services services) {

        final boolean satisfiabilityGuard = true; // XXX
        List<LocationVariable> heaps = HeapContext.getModHeaps(services, false);
        ProgramVariable self = (!target.isStatic() ? originalSelfVar : null);

        Name tacletName = MiscTools.toValidTacletName(name);
        TacletGenerator TG = TacletGenerator.getInstance();
        return TG.generateContractAxiomTaclets(tacletName,
                                               originalPre,
                                               originalPost,
                                               originalMby,
                                               kjt,
                                               target,
                                               heaps,
                                               self,
                                               originalResultVar,
                                               atPreVars,
                                               originalParamVars,
                                               toLimit,
                                               satisfiabilityGuard,
                                               services);
    }

    public ImmutableSet<Pair<Sort, IObserverFunction>> getUsedObservers(Services services) {
        return MiscTools.collectObservers(originalPre).union(MiscTools.collectObservers(originalPost));
    }

    public String getName() {
        return name;
    }

    public IObserverFunction getTarget() {
        return target;
    }

    public KeYJavaType getKJT() {
        return kjt;
    }

    public VisibilityModifier getVisibility() {
        return visibility;
    }

}
