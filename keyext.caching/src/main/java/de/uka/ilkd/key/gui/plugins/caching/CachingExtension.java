/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
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
import de.uka.ilkd.key.proof.reference.CopyReferenceResolver;
import de.uka.ilkd.key.proof.reference.ReferenceSearcher;
import de.uka.ilkd.key.proof.replay.CopyingProofReplayer;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;

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
    private ReferenceSearchButton referenceSearchButton;
    private CachingToggleAction toggleAction = null;
    private CachingPruneHandler cachingPruneHandler = null;

    private void initActions(MainWindow mainWindow) {
        if (toggleAction == null) {
            toggleAction = new CachingToggleAction(mainWindow);
        }
    }

    /**
     * Update the GUI state of the status line button.
     *
     * @param proof the currently open proof
     */
    public void updateGUIState(Proof proof) {
        referenceSearchButton.updateState(proof);
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
        return List.of(toggleAction);
    }

    public boolean getProofCachingEnabled() {
        return toggleAction.isSelected();
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        Proof p = e.getSource().getSelectedProof();
        if (p == null || trackedProofs.contains(p)) {
            return;
        }
        trackedProofs.add(p);
        p.addRuleAppListener(this);
        p.addProofDisposedListener(this);
        p.addProofTreeListener(cachingPruneHandler);
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
            try {
                c = ReferenceSearcher.findPreviousProof(mediator.getCurrentlyOpenedProofs(),
                    goal.node());
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
        cachingPruneHandler = new CachingPruneHandler(mediator);
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
            actions.add(new RemoveCachingInformationAction(mediator, node));
            return actions;
        } else if (kind.getType() == Proof.class) {
            Proof proof = (Proof) underlyingObject;
            List<Action> actions = new ArrayList<>();
            actions.add(new CloseAllByReference(this, mediator, proof));
            return actions;
        }
        return new ArrayList<>();
    }

    @Override
    public List<JComponent> getStatusLineComponents() {
        referenceSearchButton = new ReferenceSearchButton(mediator);
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
        // unmark interactive goals
        if (p.countNodes() > 1 && p.openGoals().stream()
                .anyMatch(goal -> goal.node().lookup(ClosedBy.class) != null)) {
            // mark goals as automatic again
            p.openGoals().stream().filter(goal -> goal.node().lookup(ClosedBy.class) != null)
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
                    CopyReferenceResolver.copyCachedGoals(newProof, referencedProof, null, null);
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

    @Override
    public SettingsProvider getSettings() {
        return new CachingSettingsProvider();
    }
}
