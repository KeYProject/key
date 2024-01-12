/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.Contract;

import org.key_project.util.collection.ImmutableSet;

/**
 *
 * A variable condition that is satisfied if the two arguments are
 * <ul>
 * <li>schema variables,</li>
 * <li>their instantiations are terms of observer functions,</li>
 * <li>with the same function,</li>
 * <li>which as exactly one heap argument</li>
 * <li>and has got a dependency contract</li>
 * </ul>
 * ,
 *
 * <h3>Limitations</h3>
 *
 * Currently, this and {@link de.uka.ilkd.key.rule.metaconstruct.ObserverEqualityMetaConstruct} only
 * support observers with a single heap argument, that should be generalised.
 *
 * @author Mattias Ulbrich, 2019
 * @see de.uka.ilkd.key.rule.metaconstruct.ObserverEqualityMetaConstruct
 */
public final class SameObserverCondition implements VariableCondition {

    /**
     * The first argument provided to the condition in the rule.
     */
    private final SchemaVariable schema1;

    /**
     * The second argument provided to the condition in the rule.
     */
    private final SchemaVariable schema2;

    /**
     * Create a new condition
     *
     * @param schema1 first argument, must be schema variable
     * @param schema2 2nd argument, must be schema variable
     * @throws IllegalArgumentException if the args are not schema variables.
     */
    public SameObserverCondition(ParsableVariable schema1, ParsableVariable schema2) {
        try {
            this.schema1 = (SchemaVariable) schema1;
            this.schema2 = (SchemaVariable) schema2;
        } catch (ClassCastException e) {
            throw new IllegalArgumentException("Arguments to \\sameObserver must be term SV", e);
        }
    }


    // explanation see class javadoc.
    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate, MatchConditions mc,
            Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        final Term term1 = (Term) svInst.getInstantiation(schema1);
        final Term term2 = (Term) svInst.getInstantiation(schema2);

        if ((term1 != null && !(term1.op() instanceof IObserverFunction))
                || (term2 != null && !(term2.op() instanceof IObserverFunction))) {
            // if terms are present, they must be observer calls.
            return null;
        }

        if (term1 == null || term2 == null) {
            return mc;
        }

        IObserverFunction obs1 = (IObserverFunction) term1.op();
        IObserverFunction obs2 = (IObserverFunction) term2.op();

        if (obs1 != obs2) {
            return null;
        }

        if (obs1.getHeapCount(services) != 1 || obs1.getStateCount() != 1) {
            return null;
        }

        KeYJavaType kjt = obs1.isStatic() ? obs1.getContainerType()
                : services.getTypeConverter().getKeYJavaType(term1.sub(1));

        ImmutableSet<Contract> contracts =
            UseDependencyContractRule.getApplicableContracts(services, kjt, obs1);

        if (contracts == null || contracts.isEmpty()) {
            return null;
        }

        return mc;
    }

    @Override
    public String toString() {
        return "\\sameObserver (" + schema1 + ", " + schema2 + ")";
    }
}
