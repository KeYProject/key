/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule;

import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.Pair;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public abstract class AbstractContractRuleApp<T extends BuiltInRule>
        extends AbstractBuiltInRuleApp<T> {

    protected final @Nullable Contract instantiation;

    protected AbstractContractRuleApp(T rule, @Nullable PosInOccurrence pio) {
        this(rule, pio, null);
    }

    protected AbstractContractRuleApp(T rule, @Nullable PosInOccurrence pio,
            @Nullable Contract contract) {
        this(rule, pio, ImmutableList.nil(), contract);
    }

    protected AbstractContractRuleApp(T rule,
            @Nullable PosInOccurrence pio,
            ImmutableList<PosInOccurrence> ifInsts,
            @Nullable Contract contract) {
        super(rule, pio, ifInsts);
        this.instantiation = contract;
    }

    public @Nullable Contract getInstantiation() {
        return instantiation;
    }

    public @Nullable AbstractContractRuleApp<T> check(Services services) {
        if (instantiation != null && posInOccurrence() != null) {
            IObserverFunction target = instantiation.getTarget();
            IObserverFunction observerFunctionAtPos =
                Objects.requireNonNull(getObserverFunction(services),
                    "no observer function for the applied contract rule");
            final SpecificationRepository specRepo = services.getSpecificationRepository();

            target = specRepo.unlimitObs(target);
            observerFunctionAtPos = specRepo.unlimitObs(observerFunctionAtPos);

            if (!target.equals(observerFunctionAtPos)) {
                final KeYJavaType containerTypeAtPos = Objects.requireNonNull(
                    observerFunctionAtPos.getContainerType(),
                    "no container type for the observer function at the position");
                final KeYJavaType targetContainerType = Objects.requireNonNull(
                    target.getContainerType(),
                    "no container type for the target observer function");
                if (!specRepo.getOverridingTargets(containerTypeAtPos, observerFunctionAtPos)
                        .contains(new Pair<>(targetContainerType, target))) {
                    return null;
                }
            }
        }
        return this;
    }

    @Override
    public abstract AbstractContractRuleApp<T> tryToInstantiate(Goal goal);


    public abstract AbstractContractRuleApp<T> setContract(@Nullable Contract contract);

    public boolean complete() {
        return super.complete() && pio != null && instantiation != null;
    }

    public abstract @Nullable IObserverFunction getObserverFunction(Services services);
}
