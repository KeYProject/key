/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;


import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

/**
 * Represents an axiom specified in a class.
 *
 * @author bruns
 *
 */
public final class ClassAxiomImpl extends ClassAxiom {


    private final String name;
    private final KeYJavaType kjt;
    private final VisibilityModifier visibility;
    private final Term originalRep;
    private final ProgramVariable originalSelfVar;

    /**
     * JML axioms may not be declared static, but they may be used like static specifications. This
     * is the case when it does not refer to an instance.
     */
    private final boolean isStatic;


    public ClassAxiomImpl(String name, KeYJavaType kjt, VisibilityModifier visibility, Term rep,
            ProgramVariable selfVar) {
        assert name != null;
        assert kjt != null;
        this.name = name;
        this.kjt = kjt;
        this.visibility = visibility;
        this.originalRep = rep;
        this.originalSelfVar = selfVar;
        final OpCollector oc = new OpCollector();
        originalRep.execPostOrder(oc);
        this.isStatic = !oc.contains(originalSelfVar);
    }


    public ClassAxiomImpl(String name, String displayName, KeYJavaType kjt,
            VisibilityModifier visibility, Term rep, ProgramVariable selfVar) {
        this(name, kjt, visibility, rep, selfVar);
        this.displayName = displayName;
    }

    @Override
    public ClassAxiomImpl map(UnaryOperator<Term> op, Services services) {
        return new ClassAxiomImpl(name, name, kjt, visibility, op.apply(originalRep),
            originalSelfVar);
    }


    @Override
    public boolean equals(Object o) {
        if (o == null || this.getClass() != o.getClass()) {
            return false;
        }
        final ClassAxiomImpl other = (ClassAxiomImpl) o;

        if (isStatic != other.isStatic) {
            return false;
        }
        if (!name.equals(other.name)) {
            return false;
        }
        if (!kjt.equals(other.kjt)) {
            return false;
        }
        if (originalSelfVar != null) {
            // not interested in names
            if (other.originalSelfVar == null) {
                return false;
            } else {
                return originalSelfVar.getKeYJavaType()
                        .equals(other.originalSelfVar.getKeYJavaType());
            }
        }
        return true;
    }

    @Override
    public int hashCode() {
        return 17 * (name.hashCode() + 17 * kjt.hashCode()) + (isStatic ? 13 : 7);
    }

    @Override
    public String getName() {
        return name;
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
            Services services) {
        ImmutableList<ProgramVariable> replaceVars = ImmutableSLList.nil();
        replaceVars = replaceVars.append(services.getTypeConverter().getHeapLDT().getHeap());
        if (!isStatic) {
            replaceVars = replaceVars.append(originalSelfVar);
        }
        Term rep = services.getTermBuilder().convertToFormula(originalRep);
        TacletGenerator TG = TacletGenerator.getInstance();
        ImmutableSet<Taclet> taclets = DefaultImmutableSet.nil();
        final int c = services.getCounter("classAxiom").getCountPlusPlus();
        final String namePP = "Class axiom " + c + " in " + kjt.getFullName();
        final Name tacletName = MiscTools.toValidTacletName(namePP);
        final RuleSet ruleSet = new RuleSet(new Name("classAxiom"));
        return taclets
                .add(TG.generateAxiomTaclet(tacletName, rep, replaceVars, kjt, ruleSet, services));
    }


    @Override
    public ImmutableSet<Pair<Sort, IObserverFunction>> getUsedObservers(Services services) {
        return DefaultImmutableSet.nil();
    }


    @Override
    public String toString() {
        return "axiom " + originalRep.toString();
    }



    /**
     * Class axioms do not have targets (in opposition to represents clauses)
     */
    @Override
    public IObserverFunction getTarget() {
        return null;
    }

}
