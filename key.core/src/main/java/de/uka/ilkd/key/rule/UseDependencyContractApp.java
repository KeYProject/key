/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.logic.Term;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;
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
        this(builtInRule, pio, ImmutableList.nil(), instantiation, step);
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

    private UseDependencyContractApp computeStep(Goal goal, Services services) {
        assert this.step == null;
        final List<PosInOccurrence> steps = UseDependencyContractRule
                .getSteps(this.getHeapContext(), this.posInOccurrence(), goal.sequent(), services);
        final PosInOccurrence recorded =
            UseDependencyContractRule.findStepInIfInsts(steps, this);
        if (recorded != null) {
            return setStep(recorded);
        }
        // The step recorded on this application is not a step of this goal. The step is recorded
        // by the strategy's cost computation (DependencyContractFeature), on the application the
        // rule-application queue holds, and that same application is handed on to the goals the
        // queue is projected onto, so the recorded step is the one whichever goal was costed last
        // chose. A step is a position in a goal's sequent, so a step chosen for another goal names
        // a formula of that goal and is not found here, even when the same formula is present in
        // this one. Which goal was costed last depends on the order the goals are worked on, so
        // under the multi-core prover this is reached for some worker schedules and not others.
        //
        // The step is therefore chosen here, for the goal the application is completed on, with
        // the same policy the cost computation uses (chooseStep): of the candidate steps of this
        // goal, the first that no earlier application on this focus used. That is the choice the
        // cost computation would make on this goal, so the application is completed with the step
        // it would have been costed with, whichever goal was costed last.
        //
        // This is a pre-existing problem on main before adding MT support and just not observed
        // as often. Decision on the multi-threading branch was to fix the issue in the least
        // intrusive way, but postponing a proper fix for a follow-up issue/PR, which should
        // center on making the UseDependencyContractApp immutable and use the instantiateApp
        // path instead of assumes to provide step instantiations and cost evaluation for
        // different steps.
        final PosInOccurrence chosen = UseDependencyContractRule.chooseStep(posInOccurrence(),
            goal, getHeapContext(), services);
        if (chosen == null) {
            // the policy offers no step on this goal: the step stays unset, which keeps
            // complete() false, and the caller discards the application
            return this;
        }
        // the chosen step is recorded as the assumes instantiation too: the policy reads the steps
        // already used on a focus off the assumes instantiations of the applied rules
        return new UseDependencyContractApp<>(rule(), posInOccurrence(),
            ImmutableList.singleton(chosen), instantiation, chosen);
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
            app = app.computeStep(goal, services);
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
