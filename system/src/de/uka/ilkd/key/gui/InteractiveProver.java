// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.gui;

import java.util.Iterator;
import java.util.concurrent.CancellationException;
import java.util.concurrent.ExecutionException;

import javax.swing.SwingUtilities;
import javax.swing.SwingWorker;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.DepthFirstGoalChooserBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.AutomatedRuleApplicationManager;
import de.uka.ilkd.key.strategy.FocussedRuleApplicationManager;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.Debug;

public class InteractiveProver implements InterruptListener {

    /**
     * the proof the interactive prover works on
     */
    private Proof proof;

    /**
     * the user focused goal
     */
    private Goal focusedGoal;

    /**
     * the central strategy processor including GUI signalling
     */
    private final ApplyStrategy applyStrategy;
    private final ProverTaskListener focussedAutoModeTaskListener
            = new FocussedAutoModeTaskListener();


    /**
     * the mediator
     */
    private final KeYMediator mediator;

    private AutoModeWorker worker;

    /**
     * creates a new interactive prover object
     */
    public InteractiveProver(final KeYMediator mediator) {
        /* listens to the current selected proof and node */
        this.mediator = mediator;
        mediator.addKeYSelectionListener(new InteractiveProverKeYSelectionListener());

        mediator.getProfile().setSelectedGoalChooserBuilder(DepthFirstGoalChooserBuilder.NAME);//XXX

        applyStrategy =
                new ApplyStrategy(mediator.getProfile().getSelectedGoalChooserBuilder().create());
        applyStrategy.addProverTaskObserver(mediator().getUI());

        if (mediator.getAutoSaver() != null) {
            applyStrategy.addProverTaskObserver(mediator.getAutoSaver());
        }
    }

    /**
     * returns the KeYMediator
     */
    KeYMediator mediator() {
        return mediator;
    }

    /**
     * sets up a new proof
     *
     * @param p a Proof that contains the root of the proof tree
     */
    public void setProof(Proof p) {
        proof = p;
        if (mediator.getAutoSaver() != null) {
            mediator.getAutoSaver().setProof(p);
        }
    }

    /**
     * Apply a RuleApp and continue with update simplification or strategy
     * application according to current settings.
     *
     * @param app
     * @param goal
     */
    public void applyInteractive(RuleApp app, Goal goal) {
        goal.node().getNodeInfo().setInteractiveRuleApplication(true);
        goal.apply(app);
    }

    private long getTimeout() {
        return mediator().getAutomaticApplicationTimeout();
    }

    /**
     * returns the proof the interactive prover is working on
     *
     * @return the proof the interactive prover is working on
     */
    public Proof getProof() {
        return proof;
    }

    /**
     * starts the execution of rules with active strategy. The strategy will
     * only be applied on the goals of the list that is handed over and on the
     * new goals an applied rule adds
     */
    public void startAutoMode(ImmutableList<Goal> goals) {
        if (goals.isEmpty()) {
            mediator().notify(new GeneralInformationEvent("No enabled goals available."));
            return;
        }
        worker = new AutoModeWorker(goals);
        mediator().stopInterface(true);
        mediator().setInteractive(false);
        worker.execute();
    }

    /**
     * stops the execution of rules
     */
    @Override
    public void interruptionPerformed() {
        if (worker != null) {
            worker.cancel(true);
        }
    }

    /**
     * starts the execution of rules with active strategy. Restrict the
     * application of rules to a particular goal and (for
     * <code>focus!=null</code>) to a particular subterm or subformula of that
     * goal
     */
    public void startFocussedAutoMode(PosInOccurrence focus, Goal goal) {
        applyStrategy.addProverTaskObserver(focussedAutoModeTaskListener);

        if (focus != null) {
            // exchange the rule app manager of that goal to filter rule apps

            final AutomatedRuleApplicationManager realManager = goal.getRuleAppManager();
            goal.setRuleAppManager(null);
            final AutomatedRuleApplicationManager focusManager
                    = new FocussedRuleApplicationManager(realManager, goal, focus);
            goal.setRuleAppManager(focusManager);
        }

        startAutoMode(ImmutableSLList.<Goal>nil().prepend(goal));
    }

    private void finishFocussedAutoMode() {
        applyStrategy.removeProverTaskObserver(focussedAutoModeTaskListener);

        for (final Goal goal : proof.openGoals()) {
            // remove any filtering rule app managers that are left in the proof
            // goals
            if (goal.getRuleAppManager() instanceof FocussedRuleApplicationManager) {
                final AutomatedRuleApplicationManager focusManager
                        = (AutomatedRuleApplicationManager) goal.getRuleAppManager();
                goal.setRuleAppManager(null);
                final AutomatedRuleApplicationManager realManager
                        = focusManager.getDelegate();
                realManager.clearCache();
                goal.setRuleAppManager(realManager);
            }
        }
    }

    private final class FocussedAutoModeTaskListener implements ProverTaskListener {

        @Override
        public void taskStarted(String message, int size) {
        }

        @Override
        public void taskProgress(int position) {
        }

        @Override
        public void taskFinished(TaskFinishedInfo info) {
            SwingUtilities.invokeLater(new Runnable() {
                @Override
                public void run() {
                    finishFocussedAutoMode();
                }
            });
        }
    }

    /**
     * collects all built-in rules that are applicable at the given sequent
     * position 'pos'.
     *
     * @param pos the PosInSequent where to look for applicable rules
     */
    public ImmutableList<BuiltInRule> getBuiltInRule(PosInOccurrence pos) {
        ImmutableList<BuiltInRule> rules = ImmutableSLList.<BuiltInRule>nil();

        for (RuleApp ruleApp : getInteractiveRuleAppIndex().getBuiltInRules(focusedGoal, pos)) {
            BuiltInRule r = (BuiltInRule) ruleApp.rule();
            if (!rules.contains(r)) {
                rules = rules.prepend(r);
            }
        }
        return rules;
    }

    /**
     * @return the <code>RuleAppIndex</code> of the goal currently focussed,
     * after setting the index to unrestricted (non-automated mode)
     */
    private RuleAppIndex getInteractiveRuleAppIndex() {
        final RuleAppIndex index = focusedGoal.ruleAppIndex();
        index.autoModeStopped();
        return index;
    }

    /**
     * collects all built-in rule applications for the given rule that are
     * applicable at position 'pos' and the current user constraint
     *
     * @param rule the BuiltInRule for which the applications are collected
     * @param pos the PosInSequent the position information
     * @return a SetOf<IBuiltInRuleApp> with all possible rule applications
     */
    public ImmutableSet<IBuiltInRuleApp> getBuiltInRuleApp(BuiltInRule rule,
            PosInOccurrence pos) {

        ImmutableSet<IBuiltInRuleApp> result = DefaultImmutableSet.<IBuiltInRuleApp>nil();

        for (final IBuiltInRuleApp app : getInteractiveRuleAppIndex().
                getBuiltInRules(focusedGoal, pos)) {
            if (app.rule() == rule) {
                result = result.add(app);
            }
        }

        return result;
    }

    /**
     * collects all applications of a rule given by its name at a give position
     * in the sequent
     *
     * @param name the name of the BuiltInRule for which applications are
     * collected.
     * @param pos the position in the sequent where the BuiltInRule should be
     * applied
     * @return a SetOf<RuleApp> with all possible applications of the rule
     */
    protected ImmutableSet<IBuiltInRuleApp> getBuiltInRuleAppsForName(String name, PosInOccurrence pos) {
        ImmutableSet<IBuiltInRuleApp> result = DefaultImmutableSet.<IBuiltInRuleApp>nil();
        ImmutableList<BuiltInRule> match = ImmutableSLList.<BuiltInRule>nil();

        //get all possible rules for current position in sequent
        ImmutableList<BuiltInRule> list = getBuiltInRule(pos);

        Iterator<BuiltInRule> iter = list.iterator();

        //find all rules that match given name
        while (iter.hasNext()) {
            BuiltInRule rule = iter.next();
            if (rule.name().toString().equals(name)) {
                match = match.append(rule);
            }
        }

        iter = match.iterator();

        //find all applications for matched rules
        while (iter.hasNext()) {
            result = result.union(getBuiltInRuleApp(iter.next(), pos));
        }

        return result;
    }

    /**
     * collects all applicable NoFindTaclets of the current goal (called by the
     * SequentViewer)
     *
     * @return a list of Taclets with all applicable NoFindTaclets
     */
    ImmutableList<TacletApp> getNoFindTaclet() {
        return filterTaclet(getInteractiveRuleAppIndex().
                getNoFindTaclet(TacletFilter.TRUE,
                        mediator.getServices()), null);
    }

    /**
     * collects all applicable FindTaclets of the current goal (called by the
     * SequentViewer)
     *
     * @return a list of Taclets with all applicable FindTaclets
     */
    ImmutableList<TacletApp> getFindTaclet(PosInSequent pos) {
        if (pos != null && !pos.isSequent() && focusedGoal != null) {
            Debug.out("NoPosTacletApp: Looking for applicables rule at node",
                    focusedGoal.node().serialNr());
            return filterTaclet(getInteractiveRuleAppIndex().
                    getFindTaclet(TacletFilter.TRUE,
                            pos.getPosInOccurrence(),
                            mediator.getServices()), pos);
        }
        return ImmutableSLList.<TacletApp>nil();
    }

    /**
     * collects all applicable RewriteTaclets of the current goal (called by the
     * SequentViewer)
     *
     * @return a list of Taclets with all applicable RewriteTaclets
     */
    ImmutableList<TacletApp> getRewriteTaclet(PosInSequent pos) {
        if (!pos.isSequent()) {
            return filterTaclet(getInteractiveRuleAppIndex().
                    getRewriteTaclet(TacletFilter.TRUE,
                            pos.getPosInOccurrence(),
                            mediator.getServices()), pos);
        }

        return ImmutableSLList.<TacletApp>nil();
    }

    /**
     * collects all Taclet applications at the given position of the specified
     * taclet
     *
     * @param goal the Goal for which the applications should be returned
     * @param name the String with the taclet names whose applications are
     * looked for
     * @param pos the PosInOccurrence describing the position
     * @return a list of all found rule applications of the given rule at
     * position pos
     */
    protected ImmutableSet<TacletApp> getAppsForName(Goal goal, String name,
            PosInOccurrence pos) {
        return getAppsForName(goal, name, pos, TacletFilter.TRUE);
    }

    /**
     * collects all taclet applications for the given position and taclet
     * (identified by its name) matching the filter condition
     *
     * @param goal the Goal for which the applications should be returned
     * @param name the String with the taclet names whose applications are
     * looked for
     * @param pos the PosInOccurrence describing the position
     * @param filter the TacletFilter expressing restrictions
     * @return a list of all found rule applications of the given rule at
     * position <tt>pos</tt> passing the filter
     */
    protected ImmutableSet<TacletApp> getAppsForName(Goal goal, String name,
            PosInOccurrence pos,
            TacletFilter filter) {
        ImmutableSet<TacletApp> result = DefaultImmutableSet.<TacletApp>nil();
        ImmutableList<TacletApp> fittingApps = ImmutableSLList.<TacletApp>nil();
        final RuleAppIndex index = goal.ruleAppIndex();

        if (pos == null) {
            for (NoPosTacletApp noPosTacletApp : index.getNoFindTaclet(filter,
                    mediator.getServices())) {
                fittingApps = fittingApps.prepend(noPosTacletApp);
            }
        } else {
            fittingApps = index.getTacletAppAt(filter,
                    pos,
                    mediator.getServices());
        }

        // filter fitting applications
        for (TacletApp app : fittingApps) {
            if (app.rule().name().toString().equals(name)) {
                result = result.add(app);
            }
        }
//if (result.size()==0) System.err.println("Available was "+fittingApps);
        return result;
    }

    /**
     * listener to KeYSelection Events in order to be informed if the current
     * proof changed
     */
    private class InteractiveProverKeYSelectionListener
            implements KeYSelectionListener {

        /**
         * focused node has changed
         */
        @Override
        public void selectedNodeChanged(KeYSelectionEvent e) {
            focusedGoal = e.getSource().getSelectedGoal();
        }

        /**
         * the selected proof has changed (e.g. a new proof has been loaded)
         */
        @Override
        public void selectedProofChanged(KeYSelectionEvent e) {
            Debug.out("InteractiveProver: initialize with new proof");
            Proof newProof = e.getSource().getSelectedProof();
            setProof(newProof); // this is null-safe
            if (newProof != null) {
                focusedGoal = e.getSource().getSelectedGoal();
            } else {
                focusedGoal = null;
            }
        }

    }

    /**
     * The purpose is to reset the interactiveProver to prevent memory leaking.
     * This method is used, e.g., by
     * {@code TaskTree.removeTaskWithoutInteraction}. An alternative would be to
     * reset the InteractiveProver in
     * {@code InteractiveProverKeYSelectionListener.selectedProofChanged} but
     * there we don't know whether the proof has been abandoned or not.
     *
     * @author gladisch
     */
    public void clear() {
        if (applyStrategy != null) {
            applyStrategy.clear();
        }
        if (proof != null) {
            proof.clearAndDetachRuleAppIndexes();
            proof = null;
        }
        focusedGoal = null;
        //probably more clean up has to be done here.
    }

    /**
     * takes NoPosTacletApps as arguments and returns a duplicate free list of
     * the contained TacletApps
     */
    private ImmutableList<TacletApp> filterTaclet(
            ImmutableList<NoPosTacletApp> tacletInstances, PosInSequent pos) {
        java.util.HashSet<Taclet> applicableRules = new java.util.HashSet<Taclet>();
        ImmutableList<TacletApp> result = ImmutableSLList.<TacletApp>nil();
        for (NoPosTacletApp app : tacletInstances) {
            if (mediator().minimizeInteraction()) {
                ImmutableList<TacletApp> ifCandidates
                        = app.findIfFormulaInstantiations(
                                mediator().getSelectedGoal().sequent(),
                                mediator().getServices());
                if (ifCandidates.isEmpty()) {
                    continue; // skip this app
                }
                if (ifCandidates.size() == 1 && pos != null) {
                    TacletApp a = ifCandidates.head();
                    ImmutableList<IfFormulaInstantiation> ifs
                            = a.ifFormulaInstantiations();
                    if (ifs != null && ifs.size() == 1
                            && ifs.head() instanceof IfFormulaInstSeq) {
                        IfFormulaInstSeq ifis = (IfFormulaInstSeq) ifs.head();
                        if (ifis.toPosInOccurrence().equals(
                                pos.getPosInOccurrence().topLevel())) {
                            continue; // skip app if find and if same formula
                        }
                    }
                }
            }

            Taclet taclet = app.taclet();
            if (!applicableRules.contains(taclet)) {
                applicableRules.add(taclet);
                result = result.prepend(app);
            }
        }
        return result;
    }

    /* <p>
     * Invoking start() on the SwingWorker causes a new Thread
     * to be created that will call construct(), and then
     * finished().  Note that finished() is called even if
     * the worker is interrupted because we catch the
     * InterruptedException in doWork().
     * </p>
     * <p>
     * <b>Attention:</b> Before this thread is started it is required to
     * freeze the MainWindow via
     * {@code
     * mediator().stopInterface(true);
     *   mediator().setInteractive(false);
     * }. The thread itself unfreezes the UI when it is finished.
     * </p>
     */
    private class AutoModeWorker extends SwingWorker<ApplyStrategyInfo, Object> {

        private final ImmutableList<Goal> goals;

        public AutoModeWorker(final ImmutableList<Goal> goals) {
            this.goals = goals;
        }

        @Override
        protected void done() {
            try {
                get();
            } catch (final InterruptedException exception) {
                notifyException(exception);
            } catch (final ExecutionException exception) {
                notifyException(exception);
            } catch (final CancellationException exception) {
                // when the user canceled it's not an error
            }

            synchronized(applyStrategy) {
                // make it possible to free memory and falsify the isAutoMode() property
                worker = null;
                // wait for apply Strategy to terminate
                mediator().setInteractive(true);
                mediator().startInterface(true);
            }
        }

        private void notifyException(final Exception exception) {
            mediator().notify(new GeneralFailureEvent("An exception occurred during"
                    + " strategy execution.\n Exception:" + exception));
        }

        @Override
        protected ApplyStrategyInfo doInBackground() throws Exception {
            boolean stopMode = proof.getSettings().getStrategySettings()
                    .getActiveStrategyProperties().getProperty(
                            StrategyProperties.STOPMODE_OPTIONS_KEY)
                    .equals(StrategyProperties.STOPMODE_NONCLOSE);
            return applyStrategy.start(proof, goals, mediator().getMaxAutomaticSteps(),
                    getTimeout(), stopMode);
        }
    }
}
