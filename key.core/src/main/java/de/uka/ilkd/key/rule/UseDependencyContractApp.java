/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.logic.Term;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

public class UseDependencyContractApp<T extends UseDependencyContractRule>
        extends AbstractContractRuleApp<T> {

    private final PosInOccurrence step;
    private List<LocationVariable> heapContext;

    public UseDependencyContractApp(UseDependencyContractRule builtInRule, PosInOccurrence pio) {
        this(builtInRule, pio, null, null);
    }

    public UseDependencyContractApp(UseDependencyContractRule builtInRule, PosInOccurrence pio,
            Contract instantiation, PosInOccurrence step) {
        this(builtInRule, pio, ImmutableSLList.nil(), instantiation, step);
    }

    public UseDependencyContractApp(UseDependencyContractRule rule, PosInOccurrence pio,
            ImmutableList<PosInOccurrence> ifInsts, Contract contract,
            PosInOccurrence step) {
        // weigl: why is this unchecked cast needed?
        super((T) rule, pio, ifInsts, contract);
        this.step = step;
    }

    public UseDependencyContractApp<T> replacePos(PosInOccurrence newPos) {
        return new UseDependencyContractApp<>(rule(), newPos, ifInsts, instantiation, step);
    }

    public boolean isSufficientlyComplete() {
        return pio != null && instantiation != null && !ifInsts.isEmpty();
    }

    public boolean complete() {
        return super.complete() && step != null;
    }

    private UseDependencyContractApp computeStep(Sequent seq, Services services) {
        assert this.step == null;
        final List<PosInOccurrence> steps = UseDependencyContractRule
                .getSteps(this.getHeapContext(), this.posInOccurrence(), seq, services);
        PosInOccurrence l_step =
            UseDependencyContractRule.findStepInIfInsts(steps, this);
        assert l_step != null;/*
                               * : "The strategy failed to properly " +
                               * "instantiate the base heap!\n" + "at: " +
                               * app.posInOccurrence().subTerm() + "\n" + "ifInsts: " +
                               * app.ifInsts() + "\n" + "steps: " + steps;
                               */
        return setStep(l_step);
    }


    public PosInOccurrence step() {
        return step;
    }

    public UseDependencyContractApp<T> setStep(PosInOccurrence p_step) {
        assert this.step == null;
        return new UseDependencyContractApp<>(rule(), posInOccurrence(), assumesInsts(),
            instantiation,
            p_step);
    }

    @Override
    public UseDependencyContractApp<T> setContract(Contract contract) {
        return new UseDependencyContractApp<>(rule(), posInOccurrence(), ifInsts, contract,
            step);
    }

    public UseDependencyContractApp<T> tryToInstantiate(Goal goal) {
        if (heapContext == null) {
            heapContext = HeapContext.getModifiableHeaps(goal.proof().getServices(), false);
        }
        if (complete()) {
            return this;
        }
        UseDependencyContractApp app = this;

        final Services services = goal.proof().getServices();

        app = tryToInstantiateContract(services);

        if (!app.complete() && app.isSufficientlyComplete()) {
            app = app.computeStep(goal.sequent(), services);
        }
        return app;
    }

    public UseDependencyContractApp tryToInstantiateContract(final Services services) {
        final var focus = posInOccurrence().subTerm();
        if (!(focus.op() instanceof IObserverFunction target))
        // TODO: find more appropriate exception
        {
            throw new RuntimeException(
                "Dependency contract rule is not applicable to term " + focus);
        }

        final Term selfTerm;
        final KeYJavaType kjt;

        if (target.isStatic()) {
            selfTerm = null;
            kjt = target.getContainerType();
        } else {
            if (getHeapContext() == null) {
                heapContext = HeapContext.getModifiableHeaps(services, false);
            }
            selfTerm = focus.sub(target.getStateCount() * target.getHeapCount(services));
            kjt = services.getJavaInfo().getKeYJavaType(selfTerm.sort());
        }
        ImmutableSet<Contract> contracts =
            UseDependencyContractRule.getApplicableContracts(services, kjt, target);

        if (!contracts.isEmpty()) {
            UseDependencyContractApp r = setContract(contracts.iterator().next());
            if (r.getHeapContext() == null) {
                r.heapContext = HeapContext.getModifiableHeaps(services, false);
            }
            return r;
        }
        return this;
    }

    @Override
    public List<LocationVariable> getHeapContext() {
        return heapContext;
    }

    @Override
    public IObserverFunction getObserverFunction(Services services) {
        final var op = posInOccurrence().subTerm().op();
        return (IObserverFunction) (op instanceof IObserverFunction ? op : null);
    }



    @Override
    public UseDependencyContractApp setAssumesInsts(
            ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
        // return new UseDependencyContractApp(builtInRule, pio, ifInsts, instantiation, step);
    }



}
