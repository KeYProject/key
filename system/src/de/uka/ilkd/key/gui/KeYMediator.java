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
import java.util.LinkedList;

import javax.swing.Action;
import javax.swing.SwingUtilities;
import javax.swing.event.EventListenerList;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.notification.events.ExceptionFailureEvent;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.gui.notification.events.ProofClosedNotificationEvent;
import de.uka.ilkd.key.gui.utilities.CheckedUserInput;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.delayedcut.DelayedCut;
import de.uka.ilkd.key.proof.delayedcut.DelayedCutListener;
import de.uka.ilkd.key.proof.delayedcut.DelayedCutProcessor;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.io.AutoSaver;
import de.uka.ilkd.key.proof.join.JoinProcessor;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.ui.UserInterface;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.GuiUtilities;
import de.uka.ilkd.key.util.KeYExceptionHandler;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;
import de.uka.ilkd.key.util.MiscTools;


public class KeYMediator {

    /** The user interface */
    private UserInterface ui;

    private InteractiveProver interactiveProver;

    /** the notation info used to print sequents */
    private final NotationInfo notationInfo;

    /** listenerList with to gui listeners */
    private EventListenerList listenerList = new EventListenerList();

    /** listens to the proof */
    private KeYMediatorProofListener proofListener;

    /** listens to the ProofTree */
    private KeYMediatorProofTreeListener proofTreeListener;

    /** current proof and node the user works with. All user
     * interaction is relative to this model
     */
    private KeYSelectionModel keySelectionModel;

    private KeYExceptionHandler defaultExceptionHandler;

    private boolean minimizeInteraction; // minimize user interaction

    private TacletFilter filterForInteractiveProving;
    
    /**
     * The currently used {@link OneStepSimplifier} which has to be changed
     * when the current {@link Proof} lives in a different {@link Profile}
     * than the {@link Proof} before.
     */
    private OneStepSimplifier currentOneStepSimplifier;

    /**
     * An optional used {@link AutoSaver}.
     */
    private AutoSaver autoSaver;


    /** creates the KeYMediator with a reference to the application's
     * main frame and the current proof settings
     */
    public KeYMediator(UserInterface ui) {
	this.ui             = ui;
	this.autoSaver = AutoSaver.getDefaultInstance();

	notationInfo        = new NotationInfo();
	proofListener       = new KeYMediatorProofListener();
	proofTreeListener   = new KeYMediatorProofTreeListener();
	keySelectionModel   = new KeYSelectionModel();
	interactiveProver   = new InteractiveProver(this);

	addAutoModeListener(proofListener);

	defaultExceptionHandler = new KeYRecoderExcHandler();

	// There may be other interruption listeners, but the interaction
	// engine listens by default.
	addInterruptedListener(interactiveProver);
    }


    /** returns the used NotationInfo
     * @return the used NotationInfo
     */
    public NotationInfo getNotationInfo() {
	return notationInfo;
    }

    public KeYExceptionHandler getExceptionHandler(){
	if(getSelectedProof() != null){
	    return getServices().getExceptionHandler();
	}else{
	    return defaultExceptionHandler;
	}
    }

    /** returns the variable namespace
     * @return the variable namespace
     */
    public Namespace var_ns() {
       NamespaceSet namespaces = namespaces();
       return namespaces != null ? namespaces.variables() : null;
    }

    /** returns the program variable namespace
     * @return the program variable namespace
     */
    public Namespace progVar_ns() {
       NamespaceSet namespaces = namespaces();
       return namespaces != null ? namespaces.programVariables() : null;
    }

    /** returns the function namespace
     * @return the function namespace
     */
    public Namespace func_ns() {
       NamespaceSet namespaces = namespaces();
       return namespaces != null ? namespaces.functions() : null;
    }

    /** returns the sort namespace
     * @return the sort namespace
     */
    public Namespace sort_ns() {
       NamespaceSet namespaces = namespaces();
       return namespaces != null ? namespaces.sorts() : null;
    }

    /** returns the heuristics namespace
     * @return the heuristics namespace
     */
    public Namespace heur_ns() {
       NamespaceSet namespaces = namespaces();
       return namespaces != null ? namespaces.ruleSets() : null;
    }

    /** returns the choice namespace
     * @return the choice namespace
     */
    public Namespace choice_ns() {
       NamespaceSet namespaces = namespaces();
       return namespaces != null ? namespaces.choices() : null;
    }

    /** returns the prog var namespace
     * @return the prog var namespace
     */
    public Namespace pv_ns() {
       NamespaceSet namespaces = namespaces();
       return namespaces != null ? namespaces.programVariables() : null;
    }

    /** returns the namespace set
     * @return the  namespace set
     */
    public NamespaceSet namespaces() {
       Proof selectedProof = getSelectedProof();
       return selectedProof != null ? selectedProof.getNamespaces() : null;
    }

    /** returns the JavaInfo with the java type information */
    public JavaInfo getJavaInfo() {
       Proof selectedProof = getSelectedProof();
       return selectedProof != null ? selectedProof.getJavaInfo() : null;
    }

    /** returns the Services with the java service classes */
    public Services getServices() {
       Proof selectedProof = getSelectedProof();
       return selectedProof != null ? selectedProof.getServices() : null;
    }

    /** simplified user interface? */
    public boolean minimizeInteraction() {
       return minimizeInteraction;
    }

    public void setMinimizeInteraction(boolean b) {
       minimizeInteraction = b;
    }

    public boolean ensureProofLoaded() {
    	return getSelectedProof() != null;
    }

    /**
     * Returns a filter that is used for filtering taclets that should not be showed while
     * interactive proving.
     */
    public TacletFilter getFilterForInteractiveProving() {
    	if(filterForInteractiveProving == null){
    		filterForInteractiveProving = new TacletFilter(){

				@Override
				protected boolean filter(Taclet taclet) {
					for(String name : JoinProcessor.SIMPLIFY_UPDATE){
						if(name.equals(taclet.name().toString())){
							return false;
						}
					}
					return true;
				}

    		};
    	}
    	return filterForInteractiveProving;
	}

    /** Undo.
     * @author VK
     */
    public void setBack() {
	if (ensureProofLoaded()) {
	    setBack(getSelectedGoal());
	}
    }

    public void setBack(Node node) {
    	node.proof().pruneProof(node);
    	finishSetBack(node.proof());
    }

    public void setBack(Goal goal) {
    	if (getSelectedProof() != null) {
    		goal.proof().pruneProof(goal);
    		finishSetBack(goal.proof());

    	}
    }


    private void finishSetBack(final Proof proof){
        TaskFinishedInfo info =
                new DefaultTaskFinishedInfo(this, null, proof, 0, 0,
                                            getNrGoalsClosedByAutoMode()) {
            @Override
            public String toString() {
                return "Proof has been pruned: "+(proof.openGoals().size() == 1 ?
                        "one open goal remains." :
                            (proof.openGoals().size()+" open goals remain."));
            }
        };
        this.ui.taskFinished(info);
        if (!proof.isDisposed()) {
           ServiceCaches caches = proof.getServices().getCaches();
           caches.getTermTacletAppIndexCache().clear();
           caches.getBetaCandidates().clear(); // TODO: Is this required since the strategy is instantiated everytime again?
           caches.getIfThenElseMalusCache().clear(); // TODO: Is this required since the strategy is instantiated everytime again?
        }
    }


    /**
     * initializes proof (this is Swing thread-safe)
     */
    public void setProof(Proof p) {
        final Proof pp = p;
        if (SwingUtilities.isEventDispatchThread()) {
	    setProofHelper(pp);
        } else {
            Runnable swingProzac = new Runnable() {
               public void run() { setProofHelper(pp); }
            };
            GuiUtilities.invokeAndWait(swingProzac);
        }
    }


    private void setProofHelper(Proof newProof) {
        Proof oldProof = getSelectedProof();
        if (oldProof != null) {
            oldProof.removeProofTreeListener(proofTreeListener);
            oldProof.removeRuleAppListener(proofListener);
        }
        if (newProof != null) {
            notationInfo.setAbbrevMap(newProof.abbreviations());
        }
        if (newProof != null) {
            newProof.addProofTreeListener(proofTreeListener);
            newProof.addRuleAppListener(proofListener);
        }

        // moved from layout main here; but does not actually belong here at all;
        // we should get that rule to behave like a normal built-in rule
        OneStepSimplifier newSimplifier = MiscTools.findOneStepSimplifier(newProof);
        if (currentOneStepSimplifier != newSimplifier) {
            if (currentOneStepSimplifier != null) {
                removeKeYSelectionListener(currentOneStepSimplifier);
            }
            currentOneStepSimplifier = newSimplifier;
            if (currentOneStepSimplifier != null) {
                addKeYSelectionListener(currentOneStepSimplifier);
            }
        }

        keySelectionModel.setSelectedProof(newProof);
    }


    /**
     * Get the interactive prover.
     */
    public InteractiveProver getInteractiveProver() {
	return interactiveProver;
    }


    /** sets the maximum number of rule applications allowed in
     * automatic mode
     * @param steps an int setting the limit
     */
    public void setMaxAutomaticSteps(int steps) {
       if (getSelectedProof() != null) {
           getSelectedProof().getSettings().getStrategySettings().setMaxSteps(steps);
       }
       ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(steps);
    }

    /** returns the maximum number of rule applications allowed in
     * automatic mode
     * @return the maximum number of rule applications allowed in
     * automatic mode
     */
    public int getMaxAutomaticSteps() {
        if (getSelectedProof() != null) {
            return getSelectedProof().getSettings().getStrategySettings().getMaxSteps();
        } else {
            return ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getMaxSteps();
        }
    }

    public ImmutableSet<TacletApp> getTacletApplications(Goal g, String name,
                                                PosInOccurrence p) {
       return interactiveProver.getAppsForName(g, name, p);
    }


    public ImmutableSet<TacletApp> getTacletApplications(Goal            goal,
						String          name,
                                                PosInOccurrence pos,
                                                TacletFilter    filter) {
       return interactiveProver.getAppsForName(goal, name, pos,
					       filter);
    }

    /**
     * collects all applications of a rule given by its name at a give position in the sequent
     * @param name
     * 				the name of the BuiltInRule for which applications are collected.
     * @param pos
     * 				the position in the sequent where the BuiltInRule should be applied
     * @return
     * 				a SetOf<RuleApp> with all possible applications of the rule
     */
    public ImmutableSet<IBuiltInRuleApp> getBuiltInRuleApplications(String name, PosInOccurrence pos)
    {
    	return interactiveProver.getBuiltInRuleAppsForName(name, pos);
    }

    /**
     * selected rule to apply; opens a dialog
     * @param tacletApp the TacletApp which has been selected
     * @param pos the PosInSequent describes the position where to apply the
     * rule
     */
    public void selectedTaclet(TacletApp tacletApp, PosInSequent pos) {
	Goal goal = keySelectionModel.getSelectedGoal();
        Debug.assertTrue(goal != null);
        selectedTaclet(tacletApp.taclet(), goal, pos.getPosInOccurrence());
    }


    public boolean selectedTaclet(Taclet taclet, Goal goal,
				  PosInOccurrence pos) {
	ImmutableSet<TacletApp> applics =
           getTacletApplications(goal, taclet.name().toString(), pos);
        if (applics.size() == 0) {
            notify(new GeneralFailureEvent("Taclet application failed." + taclet.name()));
           return false;
        }
	Iterator<TacletApp> it = applics.iterator();
	if (applics.size() == 1) {
	    TacletApp firstApp = it.next();
            boolean ifSeqInteraction =
               !firstApp.taclet().ifSequent().isEmpty() ;
            if (minimizeInteraction && !firstApp.complete()) {
                ImmutableList<TacletApp> ifSeqCandidates =
                    firstApp.findIfFormulaInstantiations(goal.sequent(),
		        getServices());

                if (ifSeqCandidates.size() == 1) {
                    ifSeqInteraction = false;
                    firstApp = ifSeqCandidates.head();
                }
                TacletApp tmpApp =
                    firstApp.tryToInstantiate(getServices());
                if (tmpApp != null) firstApp = tmpApp;

            }
	    if (ifSeqInteraction || !firstApp.complete()) {
	    	LinkedList<TacletApp> l = new LinkedList<TacletApp>();
	    	l.add(firstApp);
            ApplyTacletDialogModel[] models = TacletMatchCompletionDialog.completeAndApplyApp(l, goal, this);
	    	ui.completeAndApplyTacletMatch(models, goal);
	    } else {
	    	applyInteractive(firstApp, goal);
	    }
	} else if (applics.size() > 1) {
            java.util.List<TacletApp> appList = new java.util.LinkedList<TacletApp>();

	    for (int i = 0; i < applics.size(); i++) {
	        TacletApp rapp = it.next();
                appList.add(rapp);
            }

            if (appList.size()==0) {
                 assert false;
                 return false;
            }

            ApplyTacletDialogModel[] models = TacletMatchCompletionDialog.completeAndApplyApp(
                    appList, goal, this);

            ui.completeAndApplyTacletMatch(models, goal);

        }
        return true;
    }


    /** selected rule to apply
     * @param rule the selected built-in rule
     * @param pos the PosInSequent describes the position where to apply the
     * rule
     * @param forced a boolean indicating that if the rule is complete or can be made complete
     * automatically then the rule should be applied automatically without asking the user at all
     * (e.g. if a loop invariant is available do not ask the user to provide one)
     */
    public void selectedBuiltInRule(BuiltInRule rule, PosInOccurrence pos, boolean forced) {
    	Goal goal = keySelectionModel.getSelectedGoal();
    	assert goal != null;

    	ImmutableSet<IBuiltInRuleApp> set = interactiveProver.
    			getBuiltInRuleApp(rule, pos);
    	if (set.size() > 1) {
    		System.err.println("keymediator:: Expected a single app. If " +
    				"it is OK that there are more than one " +
    				"built-in rule apps. You have to add a " +
    				"selection dialog here");
    		System.err.println("keymediator:: Ambigous applications, " +
    				"taking the first in list.");
    	}

    	IBuiltInRuleApp app = set.iterator().next();

    	if (!app.complete()) {
    		app = ui.completeBuiltInRuleApp(app, goal, forced);
    	}

    	if (app != null && app.rule() == rule) {
    		goal.apply(app);
    		return;
    	}
    }


    /**
     * Apply a RuleApp and continue with update simplification or strategy
     * application according to current settings.
     * @param app
     * @param goal
     */
    public void applyInteractive(RuleApp app, Goal goal) {
        interactiveProver.applyInteractive(app, goal);
    }



    /** collects all applicable FindTaclets of the current goal
     * (called by the SequentViewer)
     * @return a list of Taclets with all applicable FindTaclets
     */

    public ImmutableList<TacletApp> getFindTaclet(PosInSequent pos) {
    	return interactiveProver.getFindTaclet(pos);
    }

    /** collects all applicable RewriteTaclets of the current goal
     * (called by the SequentViewer)
     * @return a list of Taclets with all applicable RewriteTaclets
     */
    public ImmutableList<TacletApp> getRewriteTaclet(PosInSequent pos) {
    	return interactiveProver.getRewriteTaclet(pos);
    }

    /** collects all applicable NoFindTaclets of the current goal
     * (called by the SequentViewer)
     * @return a list of Taclets with all applicable NoFindTaclets
     */
    public ImmutableList<TacletApp> getNoFindTaclet() {
    	return interactiveProver.getNoFindTaclet();
    }

    /** collects all built-in rules
     * @return a list of all applicable built-in rules
     */
    public ImmutableList<BuiltInRule> getBuiltInRule(PosInOccurrence pos) {
	return interactiveProver.getBuiltInRule
	    (pos);
    }

    /** adds a listener to the KeYSelectionModel, so that the listener
     * will be informed if the proof or node the user has selected
     * changed
     * @param listener the KeYSelectionListener to add
     */
    public void addKeYSelectionListener(KeYSelectionListener listener) {
	keySelectionModel.addKeYSelectionListener(listener);
    }

    /** removes a listener from the KeYSelectionModel
     * @param listener the KeYSelectionListener to be removed
     */
    public void removeKeYSelectionListener(KeYSelectionListener listener) {
	keySelectionModel.removeKeYSelectionListener(listener);
    }

    /** adds a listener to GUI events
     * @param listener the GUIListener to be added
     */
    public void addGUIListener(GUIListener listener) {
	listenerList.add(GUIListener.class, listener);
    }

    /** adds a listener to GUI events
     * @param listener the GUIListener to be added
     */
    public void removeGUIListener(GUIListener listener) {
	listenerList.remove(GUIListener.class, listener);
    }

    public void addAutoModeListener(AutoModeListener listener) {
	interactiveProver.addAutoModeListener(listener);
    }

    public void removeAutoModeListener(AutoModeListener listener) {
	interactiveProver.removeAutoModeListener(listener);
    }

    public void addInterruptedListener(InterruptListener listener) {
        listenerList.add(InterruptListener.class, listener);
    }

    public void removeInterruptedListener(InterruptListener listener) {
        listenerList.remove(InterruptListener.class, listener);
    }

    /** sets the current goal
     * @param goal the Goal being displayed in the view of the sequent
     */
    public void goalChosen(Goal goal) {
	keySelectionModel.setSelectedGoal(goal);
    }

    /** returns the user interface
     * @return the user interface
     */
    public UserInterface getUI() {
        return ui;
    }

    /** notifies that a node that is not a goal has been chosen
     * @param node the node being displayed in the view of the sequent
     */
    public void nonGoalNodeChosen(Node node) {
	keySelectionModel.setSelectedNode(node);
    }

    /** called to ask for modal access
     * @param src Object that is the asking component
     */
    public synchronized void requestModalAccess(Object src) {
	fireModalDialogOpened(new GUIEvent(src));
    }

    /** called if no more modal access is needed
    * @param src Object that is the asking component
     */
    public synchronized void freeModalAccess(Object src) {
	fireModalDialogClosed(new GUIEvent(src));
    }

    /** fires the request of a GUI component for modal access
     * this can be used to disable all views even if the GUI component
     * has no built in modal support
     */
    public synchronized void fireModalDialogOpened(GUIEvent e) {
	Object[] listeners = listenerList.getListenerList();
	for (int i = listeners.length-2; i>=0; i-=2) {
	    if (listeners[i] == GUIListener.class) {
		((GUIListener)listeners[i+1]).modalDialogOpened(e);
	    }
	}
    }

    /** fires that a GUI component that has asked for modal access
     * has been closed, so views can be enabled again
     */
    public synchronized void fireModalDialogClosed(GUIEvent e) {
	Object[] listeners = listenerList.getListenerList();
	for (int i = listeners.length-2; i>=0; i-=2) {
	    if (listeners[i] == GUIListener.class) {
		((GUIListener)listeners[i+1]).modalDialogClosed(e);
	    }
	}
    }

    /** Fires the shut down event.
     */
    public synchronized void fireShutDown(GUIEvent e) {
	Object[] listeners = listenerList.getListenerList();
	for (int i = listeners.length-2; i>=0; i-=2) {
	    if (listeners[i] == GUIListener.class) {
		((GUIListener)listeners[i+1]).shutDown(e);
	    }
	}
    }


    /** returns the current selected proof
     * @return the current selected proof
     * @see #getProof()
     */
    public Proof getSelectedProof() {
 	return keySelectionModel.getSelectedProof();
    }

    /** returns the current selected goal
     * @return the current selected goal
     */
    public Goal getSelectedGoal() {
 	return keySelectionModel.getSelectedGoal();
    }

   /** returns the current selected goal
     * @return the current selected goal
     */
    public KeYSelectionModel  getSelectionModel() {
 	return keySelectionModel;
    }

    /** returns the current selected node
     * @return the current selected node
     */
    public Node getSelectedNode() {
 	return keySelectionModel.getSelectedNode();
    }

    /**
     * Start automatic application of rules on open goals.
     */
    public void startAutoMode() {
	if (ensureProofLoaded()) {
	    startAutoMode(getSelectedProof().openEnabledGoals());
	}
    }

    /**
     * Start automatic application of rules on specified goals.
     * @param goals
     */
    public void startAutoMode(ImmutableList<Goal> goals) {
       interactiveProver.startAutoMode(goals);
    }

    /**
     * Stop automatic application of rules.
     */
    public void stopAutoMode() {
        for (InterruptListener listener :
               listenerList.getListeners(InterruptListener.class)) {
            listener.interruptionPerformed();
        }
    }

    /**
     * Switches interactive mode on or off.
     * @param b true iff interactive mode is to be turned on
     */
    public void setInteractive ( boolean b ) {
        if (getSelectedProof() != null) {
            if ( b  ) {
                getSelectedProof().setRuleAppIndexToInteractiveMode ();
            } else {
                getSelectedProof().setRuleAppIndexToAutoMode ();
            }
        }
    }

    private int goalsClosedByAutoMode=0;

    public void closedAGoal() {
	    goalsClosedByAutoMode++;
    }

    public int getNrGoalsClosedByAutoMode() {
	return goalsClosedByAutoMode;
    }

    public void resetNrGoalsClosedByHeuristics() {
	goalsClosedByAutoMode=0;
    }


   public void stopInterface(boolean fullStop) {
      final boolean b = fullStop;
      Runnable interfaceSignaller = new Runnable() {
         public void run() {
            ui.notifyAutoModeBeingStarted();
            if (b) {
               interactiveProver.fireAutoModeStarted(
                  new ProofEvent(getSelectedProof()));
            }
         }
      };
      GuiUtilities.invokeAndWait(interfaceSignaller);
   }

   public void startInterface(boolean fullStop) {
      final boolean b = fullStop;
      Runnable interfaceSignaller = new Runnable() {
         public void run() {
            if ( b )
               interactiveProver.fireAutoModeStopped (new ProofEvent(getSelectedProof()));
            ui.notifyAutomodeStopped();
            if (getSelectedProof() != null)
                keySelectionModel.fireSelectedProofChanged();
         }
      };
      GuiUtilities.invokeAndWait(interfaceSignaller);
   }

    public boolean autoMode() {
        return interactiveProver.isAutoMode();
    }

    class KeYMediatorProofTreeListener extends ProofTreeAdapter {
    	private boolean pruningInProcess;

    	public void proofClosed(ProofTreeEvent e) {
    		KeYMediator.this.notify
    		(new ProofClosedNotificationEvent(e.getSource()));
    	}

    	public void proofPruningInProcess(ProofTreeEvent e) {
    		pruningInProcess = true;
    	}

    	public void proofPruned(final ProofTreeEvent e) {
    		SwingUtilities.invokeLater(new Runnable() {
    			public void run () {
    				if (!e.getSource().find(getSelectedNode())) {
    					keySelectionModel.setSelectedNode(e.getNode());
    				}
    			}});
    		pruningInProcess = false;
    	}

    	public void proofGoalsAdded(ProofTreeEvent e) {
    		ImmutableList<Goal> newGoals = e.getGoals();
    		// Check for a closed goal ...
    		if (newGoals.size() == 0){
    			// No new goals have been generated ...
    			closedAGoal();
    		}
    	}

    	public void proofStructureChanged(ProofTreeEvent e) {
    		if (autoMode() || pruningInProcess) return;
    		Proof p = e.getSource();
    		if (p == getSelectedProof()) {
    			Node sel_node = getSelectedNode();
    			if (!p.find(sel_node)) {
    				keySelectionModel.defaultSelection();
    			} else {
    				// %%% hack does need to be done proper
    				// needed top update that the selected node nay have
    				// changed its status
    				keySelectionModel.setSelectedNode(sel_node);
    			}
    		}
    	}
    }

    private final class KeYMediatorProofListener implements RuleAppListener,
                                                            AutoModeListener {

	/** invoked when a rule has been applied */
	public void ruleApplied(ProofEvent e) {
	    if (autoMode()) return;
	    if (e.getSource() == getSelectedProof()) {
	        keySelectionModel.defaultSelection();
	    }
	}


	/** invoked if automatic execution has started
	 */
	public void autoModeStarted(ProofEvent e) {
	    resetNrGoalsClosedByHeuristics();
	}

	/** invoked if automatic execution has stopped
	 */
	public void autoModeStopped(ProofEvent e) {
	}
    }

    class KeYMediatorSelectionListener implements KeYSelectionListener {
	/** focused node has changed */
	public void selectedNodeChanged(KeYSelectionEvent e) {
	    // empty
	}

	/** the selected proof has changed (e.g. a new proof has been
	 * loaded)
	 */
	public void selectedProofChanged(KeYSelectionEvent e) {
	    setProof(e.getSource().getSelectedProof());
	}
    }

    /*
     * Disable certain actions until a proof is loaded.
     */
    public void enableWhenProofLoaded(final Action a) {
        a.setEnabled(getSelectedProof() != null);
        addKeYSelectionListener(new KeYSelectionListener() {
            public void selectedNodeChanged(KeYSelectionEvent e) {}
            public void selectedProofChanged(KeYSelectionEvent e) {
                a.setEnabled(
                    e.getSource().getSelectedProof() != null);
            }
        });
    }

    /**
     * takes a notification event and informs the notification
     * manager
     * @param event the NotificationEvent
     */
    public void notify(NotificationEvent event) {
        if (ui != null) {
            ui.notify(event);
        }
    }

    /** return the chosen profile */
    public Profile getProfile() {
       Proof selectedProof = getSelectedProof();
       if (selectedProof != null) {
          return selectedProof.getServices().getProfile();
       }
       else {
          return AbstractProfile.getDefaultProfile();
       }
    }

    /**
     * besides the number of rule applications it is possible to define a timeout after which rule application
     * shall be terminated
     * @return the time in ms after which automatic rule application stops
     */
    public long getAutomaticApplicationTimeout() {
        if (getSelectedProof() != null) {
            return getSelectedProof().getSettings().getStrategySettings().getTimeout();
        } else {
            return ProofSettings.DEFAULT_SETTINGS.getStrategySettings().getTimeout();
        }
    }

    /**
     * sets the time out after which automatic rule application stops
     * @param timeout a long specifying the timeout time in ms
     */
    public void setAutomaticApplicationTimeout(long timeout) {
       if (getSelectedProof() != null) {
           getSelectedProof().getSettings().getStrategySettings().setTimeout(timeout);
       }
       ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setTimeout(timeout);
    }

//    /**
//     * returns the prover task listener of the main frame
//     */
//    // TODO used 1 time, drop it? (MU)
//    public ProverTaskListener getProverTaskListener() {
//        return ui;
//    }

    public boolean processDelayedCut(final Node invokedNode) {
        if (ensureProofLoaded()) {
            final String result =
                    CheckedUserInput.showAsDialog("Cut Formula",
                            "Please supply a formula:",
                            null,
                            "",
                    new InspectorForDecisionPredicates(getSelectedProof().getServices(),invokedNode,
                            DelayedCut.DECISION_PREDICATE_IN_ANTECEDENT,
                            DelayedCutProcessor.getApplicationChecks()), true);

            if (result == null) {
                return false;
            }

            Term formula = InspectorForDecisionPredicates.translate(getSelectedProof().getServices(),result);

            DelayedCutProcessor processor = new DelayedCutProcessor(getSelectedProof(),
                    invokedNode,
                    formula,
                    DelayedCut.DECISION_PREDICATE_IN_ANTECEDENT);
            processor.add(new DelayedCutListener() {

                @Override
                public void eventRebuildingTree(final int currentTacletNumber,final int totalNumber) {

                    SwingUtilities.invokeLater(new Runnable() {

                        @Override
                        public void run() {
                            ui.taskStarted("Rebuilding...", totalNumber);
                            ui.taskProgress(currentTacletNumber);

                         }
                    });
                }

                @Override
                public void eventEnd(DelayedCut cutInformation) {
                    SwingUtilities.invokeLater(new Runnable() {

                        @Override
                        public void run() {
                            ui.resetStatus(this);
                            KeYMediator.this.startInterface(true);
                        }
                    });

                }

                @Override
                public void eventCutting() {
                    SwingUtilities.invokeLater(new Runnable() {

                        @Override
                        public void run() {
                            ui.taskStarted("Cutting...", 0);
                        }
                    });

                }

                @Override
                public void eventException(Throwable throwable) {
                    KeYMediator.this.startInterface(true);

                    throwable.printStackTrace();
                    KeYMediator.this.notify(new ExceptionFailureEvent("The cut could" +
                            "not be processed successfully. In order to " +
                            		"preserve consistency the proof is pruned." +
                            " For more information see details or output of your console.", throwable));

                    SwingUtilities.invokeLater(new Runnable() {

                        @Override
                        public void run() {
                            getSelectedProof().pruneProof(invokedNode);
                        }
                    });
                }
            });
            this.stopInterface(true);


            Thread thread = new Thread(processor,"DelayedCutListener");
            thread.start();
        }
        return true;

    }

   /**
    * Returns the {@link AutoSaver} to use.
    * @return The {@link AutoSaver} to use or {@code null} if no {@link AutoSaver} should be used.
    */
   public AutoSaver getAutoSaver() {
      return autoSaver;
   }
}
