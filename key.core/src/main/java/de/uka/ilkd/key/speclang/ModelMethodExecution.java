/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;


public final class ModelMethodExecution extends ClassAxiom {

    private final String name;
    private final IObserverFunction target;
    private final KeYJavaType kjt;
    private final VisibilityModifier visibility;

    public ModelMethodExecution(String name, IObserverFunction target, KeYJavaType kjt,
            VisibilityModifier visibility) {
        this(name, null, target, kjt, visibility);
    }

    public ModelMethodExecution(String name, String displayName, IObserverFunction target,
            KeYJavaType kjt, VisibilityModifier visibility) {

        assert name != null;
        assert kjt != null;
        assert target != null;
        this.name = name;
        this.target = target;
        this.kjt = kjt;
        this.visibility = visibility;
        this.displayName = displayName;
    }

    @Override
    public ModelMethodExecution map(UnaryOperator<Term> op, Services services) {
        return this;
    }

    @Override
    public boolean equals(Object o) {
        if (o == null || this.getClass() != o.getClass()) {
            return false;
        }
        final ModelMethodExecution other = (ModelMethodExecution) o;

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
    public ImmutableSet<Taclet> getTaclets(ImmutableSet<Pair<Sort, IObserverFunction>> toLimit,
            Services services) {

        // Name tacletName = MiscTools.toValidTacletName(name);
        // TacletGenerator TG = TacletGenerator.getInstance();
        return null;
        // return TG.generateModelMethodExecutionTaclets(tacletName,
        // kjt,
        // target,
        // services);
    }

    @Override
    public ImmutableSet<Pair<Sort, IObserverFunction>> getUsedObservers(Services services) {
        return DefaultImmutableSet.nil();
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
