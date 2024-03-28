/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.util.*;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.help.HelpInfo;
import de.uka.ilkd.key.gui.plugins.caching.actions.CloseAllByReference;
import de.uka.ilkd.key.gui.plugins.caching.actions.CloseByReference;
import de.uka.ilkd.key.gui.plugins.caching.actions.CopyReferencedProof;
import de.uka.ilkd.key.gui.plugins.caching.actions.GotoReferenceAction;
import de.uka.ilkd.key.gui.plugins.caching.actions.RemoveCachingInformationAction;
import de.uka.ilkd.key.gui.plugins.caching.database.AutoAddClosedProofs;
import de.uka.ilkd.key.gui.plugins.caching.database.CachingDatabase;
import de.uka.ilkd.key.gui.plugins.caching.database.CachingDatabaseDialog;
import de.uka.ilkd.key.gui.plugins.caching.settings.CachingSettingsProvider;
import de.uka.ilkd.key.gui.plugins.caching.settings.ProofCachingSettings;
import de.uka.ilkd.key.gui.plugins.caching.toolbar.CachingToggleAction;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;
import de.uka.ilkd.key.proof.reference.ClosedBy;
import de.uka.ilkd.key.proof.reference.ReferenceSearcher;
import de.uka.ilkd.key.proof.replay.CopyingProofReplayer;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.settings.PathConfig;

import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Extension for proof caching.
 *
 * @author Arne Keller
 */
@KeYGuiExtension.Info(name = "Proof Caching", optional = true,
    description = "Functionality related to reusing previous proof results in similar proofs",
    experimental = false)
@HelpInfo(path = "/user/ProofCaching/")
public class CachingExtension
        implements KeYGuiExtension, KeYGuiExtension.Startup, KeYGuiExtension.ContextMenu,
        KeYGuiExtension.StatusLine, KeYGuiExtension.Settings, KeYGuiExtension.Toolbar,
        KeYGuiExtension.MainMenu,
        KeYSelectionListener, RuleAppListener, ProofDisposedListener, ProverTaskListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(CachingExtension.class);

    /**
     * The mediator.
     */
    private KeYMediator mediator;
    /**
     * Whether to try to close the current proof (by caching) after a rule application.
     * Will be false when running certain macros, like the "close provable goals" macro.
     */
    private boolean tryToClose = false;

    /**
     * Proofs tracked for automatic reference search.
     */
    private final Set<Proof> trackedProofs = new HashSet<>();
    /**
     * The reference search button in the status bar.
     */
    private ReferenceSearchButton referenceSearchButton;
    /**
     * The toggle action to quickly enable/disable proof caching.
     */
    private CachingToggleAction toggleAction = null;
    /**
     * A handler for referenced proofs that get pruned.
     */
    private CachingPruneHandler cachingPruneHandler = null;
    /**
     * A handler that automatically adds closed proofs to the database.
     */
    private AutoAddClosedProofs autoAddClosedProofs = null;
    /**
     * The external caching database (singleton instance).
     */
    private CachingDatabase database = null;

    private void initActions(MainWindow mainWindow) {
        if (toggleAction == null) {
            toggleAction = new CachingToggleAction(mainWindow);
        }
    }

    @Override
    public @NonNull JToolBar getToolbar(MainWindow mainWindow) {
        initActions(mainWindow);
        JToolBar tb = new JToolBar("Proof Caching");
        JToggleButton comp = new JToggleButton(toggleAction);
        comp.setToolTipText((String) toggleAction.getValue(Action.LONG_DESCRIPTION));
        tb.add(comp);
        return tb;
    }

    @Override
    public @NonNull List<Action> getMainMenuActions(@NonNull MainWindow mainWindow) {
        initActions(mainWindow);
        return List.of(toggleAction, CachingDatabaseDialog.getOpenAction(getDatabase()));
    }

    public boolean getProofCachingEnabled() {
        return toggleAction.isSelected();
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
        Proof p = e.getSource().getSelectedProof();
        if (p == null || trackedProofs.contains(p)) {
            return;
        }
        trackedProofs.add(p);
        p.addRuleAppListener(this);
        p.addProofDisposedListener(this);
        p.addProofTreeListener(cachingPruneHandler);
        p.addProofTreeListener(autoAddClosedProofs);
    }

    @Override
    public void ruleApplied(ProofEvent e) {
        // main entry point for proof caching logic:
        // this is called after every rule application in the proof
        if (!tryToClose) {
            return;
        }
        if (e.getSource().lookup(CopyingProofReplayer.class) != null) {
            // either:
            // copy in progress,
            // macro that excepts the proof to really close in progress
            return;
        }
        if (!CachingSettingsProvider.getCachingSettings().getEnabled()) {
            return;
        }
        // new global off switch
        if (!getProofCachingEnabled()) {
            return;
        }
        Proof p = e.getSource();
        if (e.getRuleAppInfo().getOriginalNode().getNodeInfo().getInteractiveRuleApplication()) {
            return; // only applies for automatic proof search
        }
        ImmutableList<Goal> newGoals = e.getNewGoals();
        if (newGoals.size() <= 1) {
            return;
        }
        for (Goal goal : newGoals) {
            ClosedBy c = null;
            CachedProofBranch cachedProofBranch = null;
            try {
                c = ReferenceSearcher.findPreviousProof(mediator.getCurrentlyOpenedProofs(),
                    goal.node());
                if (c == null) {
                    var cachedProofBranches = database.findMatching(
                        p.getSettings().getChoiceSettings(), goal.sequent(), p.getServices());
                    if (!cachedProofBranches.isEmpty()) {
                        cachedProofBranch = cachedProofBranches.iterator().next();
                    }
                }
            } catch (Exception exception) {
                LOGGER.warn("error during reference search ", exception);
            }
            if (c != null) {
                // stop automode from working on this goal
                goal.setEnabled(false);

                goal.node().register(c, ClosedBy.class);
                c.proof()
                        .addProofDisposedListenerFirst(
                            new CopyBeforeDispose(mediator, c.proof(), p));
            }
            if (cachedProofBranch != null) {
                goal.setEnabled(false);

                goal.node().register(cachedProofBranch, CachedProofBranch.class);
            }
        }
    }

    @Override
    public void preInit(MainWindow window, KeYMediator mediator) {
        this.mediator = mediator;
        mediator.addKeYSelectionListener(this);
        mediator.getUI().addProverTaskListener(this);
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        Runtime.getRuntime().addShutdownHook(new Thread(getDatabase()::shutdown));
        cachingPruneHandler = new CachingPruneHandler(mediator);
        autoAddClosedProofs = new AutoAddClosedProofs(database);
    }

    @Override
    public void proofDisposing(ProofDisposedEvent e) {
        trackedProofs.remove(e.getSource());
    }

    @Override
    public void proofDisposed(ProofDisposedEvent e) {

    }

    @NonNull
    @Override
    public List<Action> getContextActions(@NonNull KeYMediator mediator,
            @NonNull ContextMenuKind kind, @NonNull Object underlyingObject) {
        if (kind.getType() == Node.class) {
            Node node = (Node) underlyingObject;
            List<Action> actions = new ArrayList<>();
            actions.add(new CloseByReference(this, mediator, node));
            actions.add(new CopyReferencedProof(mediator, node));
            actions.add(new GotoReferenceAction(mediator, node));
            actions.add(new SearchInDatabaseAction(this, node));
            actions.add(new RemoveCachingInformationAction(mediator, node));
            return actions;
        } else if (kind.getType() == Proof.class) {
            Proof proof = (Proof) underlyingObject;
            List<Action> actions = new ArrayList<>();
            actions.add(new CloseAllByReference(this, mediator, proof));
            actions.add(new AddToDatabaseAction(database, proof));
            return actions;
        }
        return new ArrayList<>();
    }

    @Override
    public List<JComponent> getStatusLineComponents() {
        referenceSearchButton = new ReferenceSearchButton(this, mediator);
        return List.of(referenceSearchButton);
    }

    @Override
    public void taskStarted(TaskStartedInfo info) {
        if (info.kind().equals(TaskStartedInfo.TaskKind.Macro)
                && info.message().equals(new TryCloseMacro().getName())) {
            tryToClose = false;
        }
    }

    @Override
    public void taskProgress(int position) {
        tryToClose = true;
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        tryToClose = info.getSource() instanceof TryCloseMacro;
        if (tryToClose) {
            return; // try close macro was running, no need to do anything here
        }
        Proof p = info.getProof();
        if (p == null || p.isDisposed() || p.closed() || !(info.getSource() instanceof ApplyStrategy
                || info.getSource() instanceof ProofMacro)) {
            return;
        }
        // unmark interactive goals previously marked in ruleApplied above
        if (p.countNodes() > 1 && p.openGoals().stream()
                .anyMatch(goal -> goal.node().lookup(ClosedBy.class) != null
                        || goal.node().lookup(CachedProofBranch.class) != null)) {
            // mark goals as automatic again
            p.openGoals().stream()
                    .filter(goal -> goal.node().lookup(ClosedBy.class) != null
                            || goal.node().lookup(CachedProofBranch.class) != null)
                    .forEach(g -> {
                        g.setEnabled(true);
                        g.proof().closeGoal(g);
                    });
            // statistics dialog is automatically shown
        }
    }

    /**
     * Listener that ensures steps are copied before the referenced proof is disposed.
     *
     * @author Arne Keller
     */
    public static class CopyBeforeDispose implements ProofDisposedListener {

        /**
         * The mediator.
         */
        private final KeYMediator mediator;
        /**
         * The referenced proof.
         */
        private final Proof referencedProof;
        /**
         * The new proof.
         */
        private final Proof newProof;

        /**
         * Construct new listener.
         *
         * @param mediator the mediator
         * @param referencedProof referenced proof
         * @param newProof new proof
         */
        public CopyBeforeDispose(KeYMediator mediator, Proof referencedProof, Proof newProof) {
            this.mediator = mediator;
            this.referencedProof = referencedProof;
            this.newProof = newProof;
        }

        @Override
        public void proofDisposing(ProofDisposedEvent e) {
            if (newProof.isDisposed()) {
                return;
            }
            if (CachingSettingsProvider.getCachingSettings().getDispose()
                    .equals(ProofCachingSettings.DISPOSE_COPY)) {
                mediator.initiateAutoMode(newProof, true, false);
                try {
                    newProof.copyCachedGoals(referencedProof, null, null);
                } finally {
                    mediator.finishAutoMode(newProof, true, true,
                        /* do not select a different node */ () -> {
                        });
                }
            } else {
                newProof.closedGoals().stream()
                        .filter(x -> x.node().lookup(ClosedBy.class) != null
                                && x.node().lookup(ClosedBy.class).proof() == referencedProof)
                        .forEach(x -> {
                            newProof.reOpenGoal(x);
                            x.node().deregister(x.node().lookup(ClosedBy.class), ClosedBy.class);
                        });
            }
        }

        @Override
        public void proofDisposed(ProofDisposedEvent e) {

        }
    }

    /**
     * Update the GUI state of this extension.
     * This will update the button in the status bar.
     */
    public void updateGUIState() {
        referenceSearchButton.updateState(mediator.getSelectedProof());
    }

    @Override
    public SettingsProvider getSettings() {
        return new CachingSettingsProvider();
    }

    public CachingDatabase getDatabase() {
        if (database == null) {
            database =
                new CachingDatabase(PathConfig.getCacheIndex(), PathConfig.getCacheDirectory());
        }
        return database;
    }
}
