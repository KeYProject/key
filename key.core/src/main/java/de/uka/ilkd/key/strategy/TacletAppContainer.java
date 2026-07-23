/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.util.Debug;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstSeq;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;

/**
 * Instances of this class are immutable
 */
public abstract class TacletAppContainer extends RuleAppContainer {

    // Implementation note (DB 21/02/2014):
    // It is unlikely that we ever reach 2^31 proof nodes,
    // so age could be changed from long to int.
    // My benchmark tests however suggest that this would not
    // save any memory (at the moment).
    // This is because Java's memory alingment.

    /**
     * Creation time of this container ({@code -1} for an initial/just-loaded container). Since age
     * became a first-class container-level cost term ({@link RuleAppContainer#withAge}) this field
     * no longer feeds the cost; it is purely the {@link AssumesInstantiator} freshness key (was
     * this
     * container built before or after a given if-formula).
     */
    private final long age;
    /**
     * The age-free strategy cost: {@code getCost()} without the goal-age term that
     * {@link RuleAppContainer#withAge} adds. Stored so cost reuse can carry it forward unchanged
     * across re-expansion and only re-add the current age, with no reconstruction arithmetic.
     */
    private final RuleAppCost ageFreeCost;
    /**
     * Whether {@link #ageFreeCost} is the regular strategy cost ({@link Strategy#computeCost}) and
     * so
     * may be carried forward by cost reuse. It is {@code false} only for containers built from a
     * strategy-supplied instantiation cost ({@link Strategy#instantiateApp}, the
     * {@link #instantiateApp} collector): for those the stored cost is the instantiation score,
     * which
     * differs from a regular re-cost (e.g. an instantiated quantifier app re-costs to infinity), so
     * reusing it would be unsound. Such containers must always be re-costed normally instead.
     */
    private final boolean ageFreeCostIsRegular;

    protected TacletAppContainer(RuleApp p_app, RuleAppCost p_ageFreeCost,
            boolean p_ageFreeCostIsRegular, RuleAppCost p_cost, long p_age) {
        super(p_app, p_cost);
        ageFreeCost = p_ageFreeCost;
        ageFreeCostIsRegular = p_ageFreeCostIsRegular;
        age = p_age;
    }

    RuleAppCost getAgeFreeCost() {
        return ageFreeCost;
    }

    protected NoPosTacletApp getTacletApp() {
        return (NoPosTacletApp) getRuleApp();
    }

    public long getAge() {
        return age;
    }

    private ImmutableList<NoPosTacletApp> incMatchAssumesFormulas(Goal p_goal) {
        final AssumesInstantiator instantiator = new AssumesInstantiator(this, p_goal);
        instantiator.findAssumesFormulaInstantiations();
        return instantiator.getResults();
    }

    protected static TacletAppContainer createContainer(NoPosTacletApp p_app,
            PosInOccurrence p_pio,
            Goal p_goal, boolean p_initial) {
        // the cost is the regular strategy cost, so it may be reused
        return createContainer(p_app, p_pio, p_goal,
            p_goal.getGoalStrategy().computeCost(p_app, p_pio, p_goal), true, p_initial);
    }

    private static TacletAppContainer createContainer(NoPosTacletApp p_app,
            PosInOccurrence p_pio,
            Goal p_goal, RuleAppCost p_ageFreeCost, boolean p_ageFreeCostIsRegular,
            boolean p_initial) {
        // This relies on the fact that the method <code>Goal.getTime()</code>
        // never returns a value less than zero
        final long localage = p_initial ? -1 : p_goal.getTime();
        final RuleAppCost cost = withAge(p_ageFreeCost, p_goal);
        if (p_pio == null) {
            return new NoFindTacletAppContainer(p_app, p_ageFreeCost, p_ageFreeCostIsRegular, cost,
                localage);
        } else {
            return new FindTacletAppContainer(p_app, p_pio, p_ageFreeCost, p_ageFreeCostIsRegular,
                cost, p_goal, localage);
        }
    }

    /**
     * Create a list of new RuleAppContainers that are to be considered for application.
     */
    @Override
    public final ImmutableList<RuleAppContainer> createFurtherApps(Goal p_goal) {
        if (!isStillApplicable(p_goal)
                || (getTacletApp().assumesInstantionsComplete()
                        && !assumesFormulasStillValid(p_goal))) {
            return ImmutableList.nil();
        }

        final TacletAppContainer newCont = costLocalReusedContainerOr(p_goal);
        if (newCont == null) {
            // a veto fired on the cost-local fast path: the re-costed base would be infinite
            return ImmutableList.nil();
        }
        if (newCont.getCost() instanceof TopRuleAppCost) {
            return ImmutableList.nil();
        }

        ImmutableList<RuleAppContainer> res =
            ImmutableList.<RuleAppContainer>singleton(newCont);

        if (getTacletApp().assumesInstantionsComplete()) {
            res = addInstances(getTacletApp(), res, p_goal);
        } else {
            for (NoPosTacletApp tacletApp : incMatchAssumesFormulas(p_goal)) {
                final NoPosTacletApp app = tacletApp;
                res = addContainer(app, res, p_goal);
                res = addInstances(app, res, p_goal);
            }
        }

        return res;
    }

    /**
     * Add all instances of the given taclet app (that are possibly produced using method
     * <code>instantiateApp</code> of the strategy) to <code>targetList</code>
     */
    private ImmutableList<RuleAppContainer> addInstances(NoPosTacletApp app,
            ImmutableList<RuleAppContainer> targetList, Goal p_goal) {
        if (app.uninstantiatedVars().size() == 0) {
            return targetList;
        }
        return instantiateApp(app, targetList, p_goal);
    }

    /**
     * Use the method <code>instantiateApp</code> of the strategy for choosing the values of schema
     * variables that have not been instantiated so far
     */
    private ImmutableList<RuleAppContainer> instantiateApp(NoPosTacletApp app,
            ImmutableList<RuleAppContainer> targetList, final Goal p_goal) {
        // just for being able to modify the result-list in an
        // anonymous class
        @SuppressWarnings("unchecked")
        final ImmutableList<RuleAppContainer>[] resA = new ImmutableList[] { targetList };

        final org.key_project.prover.strategy.RuleAppCostCollector collector = (newApp, cost) -> {
            if (cost instanceof TopRuleAppCost) {
                return;
            }
            resA[0] = addContainer((NoPosTacletApp) newApp, resA[0], p_goal, cost);
        };
        p_goal.getGoalStrategy().instantiateApp(app, getPosInOccurrence(p_goal), p_goal, collector);

        return resA[0];
    }

    /**
     * Create a container object for the given taclet app, provided that the app is
     * <code>sufficientlyComplete</code>, and add the container to <code>targetList</code>
     */
    private ImmutableList<RuleAppContainer> addContainer(NoPosTacletApp app,
            ImmutableList<RuleAppContainer> targetList, Goal p_goal) {
        return targetList.prepend(
            createContainer(app, getPosInOccurrence(p_goal), p_goal, false));
    }

    /**
     * Create a container object for the given taclet app, provided that the app is
     * <code>sufficientlyComplete</code>, and add the container to <code>targetList</code>
     */
    private ImmutableList<RuleAppContainer> addContainer(NoPosTacletApp app,
            ImmutableList<RuleAppContainer> targetList, Goal p_goal, RuleAppCost cost) {
        if (!sufficientlyCompleteApp(app)) {
            return targetList;
        }
        return targetList.prepend(createContainer(app,
            getPosInOccurrence(p_goal), p_goal, cost, false, false));
    }

    private static boolean sufficientlyCompleteApp(NoPosTacletApp app) {
        final ImmutableSet<SchemaVariable> needed = app.uninstantiatedVars();
        if (needed.size() == 0) {
            return true;
        }
        for (SchemaVariable aNeeded : needed) {
            if (app.isInstantiationRequired(aNeeded)) {
                return false;
            }
        }
        return true;
    }

    private TacletAppContainer createContainer(Goal p_goal) {
        return createContainer(getTacletApp(), getPosInOccurrence(p_goal), p_goal, false);
    }

    /**
     * Re-cost the base app for {@link #createFurtherApps}. On the cost-reuse fast path (taclet
     * classified cost-local by {@link CostReuse}, numeric age-free cost) the full
     * {@link de.uka.ilkd.key.strategy.Strategy#computeCost} is skipped: the stored age-free cost is
     * carried forward verbatim and {@link RuleAppContainer#withAge} re-adds the current goal age
     * when the new container is built -- no reconstruction arithmetic, and initial containers
     * (age {@code -1}) reuse soundly too, since age is no longer part of the stored cost. The
     * {@code NonDuplicateApp}-family vetoes that contribute are re-evaluated first; if one fires
     * the
     * full cost would be {@link TopRuleAppCost}, so {@code null} is returned (drop the app).
     * Otherwise, and whenever reuse is disabled/inapplicable, falls back to the normal recompute.
     */
    private @Nullable TacletAppContainer costLocalReusedContainerOr(Goal p_goal) {
        // only a regular (computeCost) base may be carried forward; an instantiation-supplied base
        // would re-cost differently, so such containers always fall through to a normal recompute
        if (ageFreeCostIsRegular && getAgeFreeCost() instanceof NumberRuleAppCost base) {
            final CostReuse.Eligibility elig = CostReuse.eligibility(p_goal.getGoalStrategy(),
                p_goal.proof(), getTacletApp().taclet());
            // A subterm-local cost may always be carried forward; a formula-local one only while
            // the
            // find formula is unchanged (an independent sibling rewrite leaves the find subterm but
            // not the formula intact). Otherwise fall through to a normal recompute.
            if (elig != null && (!elig.weakStable() || findFormulaUnchanged(p_goal))) {
                final PosInOccurrence pos = getPosInOccurrence(p_goal);
                final MutableState mState = new MutableState();
                for (Feature veto : elig.vetoes()) {
                    if (veto.computeCost(getTacletApp(), pos, p_goal,
                        mState) instanceof TopRuleAppCost) {
                        return null;
                    }
                }
                // only for debugging or CI to raise warning flags for wrongly annotated features
                if (CostReuse.VERIFY) {
                    final RuleAppCost freshBase =
                        p_goal.getGoalStrategy().computeCost(getTacletApp(), pos, p_goal);
                    if (!base.equals(freshBase)) {
                        CostReuse.warnMismatch(getTacletApp().taclet(), base, freshBase);
                    }
                }
                // carry the age-free base forward; createContainer re-adds the current age
                return createContainer(getTacletApp(), pos, p_goal, base, true, false);
            }
        }
        return createContainer(p_goal);
    }

    /**
     * @return {@code true} iff the find formula this container was created for is still present
     *         unchanged in the goal -- the precondition for carrying forward a {@code @}
     *         {@code WeakStableCost} cost. The base container has no find formula and so
     *         conservatively answers {@code false} (such a cost is never reused for it).
     */
    protected boolean findFormulaUnchanged(Goal p_goal) {
        return false;
    }

    /**
     * Create containers for NoFindTaclets.
     */
    static RuleAppContainer createAppContainers(NoPosTacletApp p_app, Goal p_goal) {
        return createAppContainers(p_app, null, p_goal);
    }

    protected static ImmutableList<RuleAppContainer> createInitialAppContainers(
            ImmutableList<NoPosTacletApp> p_app,
            PosInOccurrence p_pio, Goal p_goal) {

        List<RuleAppCost> costs = new LinkedList<>();

        for (NoPosTacletApp app : p_app) {
            costs.add(p_goal.getGoalStrategy().computeCost(app, p_pio, p_goal));
        }

        ImmutableList<RuleAppContainer> result = ImmutableList.nil();
        for (RuleAppCost cost : costs) {
            final TacletAppContainer container =
                createContainer(p_app.head(), p_pio, p_goal, cost, true, true);
            result = result.prepend(container);
            p_app = p_app.tail();
        }
        return result;
    }

    /**
     * Create containers for FindTaclets or NoFindTaclets.
     *
     * @param p_app if <code>p_pio</code> is null, <code>p_app</code> has to be a
     *        <code>ITacletApp</code> for a <code>NoFindTaclet</code>, otherwise for a
     *        <code>FindTaclet</code>.
     * @return list of containers for currently applicable TacletApps, the cost may be an instance
     *         of <code>TopRuleAppCost</code>.
     */
    static RuleAppContainer createAppContainers(NoPosTacletApp p_app,
            PosInOccurrence p_pio,
            Goal p_goal) {
        if (!(p_pio == null ? p_app.taclet() instanceof NoFindTaclet
                : p_app.taclet() instanceof FindTaclet))
        // faster than <code>assertTrue</code>
        {
            Debug.fail("Wrong type of taclet " + p_app.taclet());
        }

        // Create an initial container for the given taclet; the if-formulas of
        // the taclet are only matched lazy (by <code>createFurtherApps()</code>
        return createContainer(p_app, p_pio, p_goal, true);
    }

    /**
     * @return true iff instantiation of the assumes-formulas of the stored taclet app exist and are
     *         valid are still valid, i.e. the referenced formulas still exist
     */
    protected boolean assumesFormulasStillValid(Goal p_goal) {
        if (getTacletApp().taclet().assumesSequent().isEmpty()) {
            return true;
        }
        if (!getTacletApp().assumesInstantionsComplete()) {
            return false;
        }

        final Iterator<AssumesFormulaInstantiation> it =
            getTacletApp().assumesFormulaInstantiations().iterator();
        final Sequent seq = p_goal.sequent();

        while (it.hasNext()) {
            final AssumesFormulaInstantiation assumesInstantiations2 = it.next();
            if (!(assumesInstantiations2 instanceof final AssumesFormulaInstSeq assumesInst))
            // faster than assertTrue
            {
                Debug.fail("Don't know what to do with the " + "assumes-instantiation ",
                    assumesInstantiations2);
                throw new IllegalStateException(
                    "Unexpected assume-instantiation" + assumesInstantiations2);
            } else if (!(assumesInst.inAntecedent() ? seq.antecedent() : seq.succedent())
                    .contains(assumesInst.getSequentFormula())) {
                return false;
            }
        }

        return true;
    }

    /**
     * @return true iff the stored rule app is applicable for the given sequent, i.e. if the
     *         find-position does still exist (assumes-formulas are not considered)
     */
    protected abstract boolean isStillApplicable(Goal p_goal);

    protected PosInOccurrence getPosInOccurrence(Goal p_goal) {
        return null;
    }

    /**
     * Create a <code>RuleApp</code> that is suitable to be applied or <code>null</code>.
     */
    @Override
    public TacletApp completeRuleApp(Goal p_goal) {
        if (!(isStillApplicable(p_goal) && assumesFormulasStillValid(p_goal))) {
            return null;
        }

        TacletApp app = getTacletApp();
        PosInOccurrence pio = getPosInOccurrence(p_goal);
        if (!p_goal.getGoalStrategy().isApprovedApp(app, pio, p_goal)) {
            return null;
        }

        Services services = p_goal.proof().getServices();
        if (pio != null) {
            app = app.setPosInOccurrence(pio, services);
            if (app == null) {
                return null;
            }
        }

        if (!app.complete()) {
            return app.tryToInstantiate(services.getOverlay(p_goal.getLocalNamespaces()));
        } else if (!app.isExecutable()) {
            return null;
        } else {
            return app;
        }
    }
}
