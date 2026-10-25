/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.exploration;

import java.awt.*;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.gui.extension.api.ContextMenuAdapter;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.help.HelpInfo;
import de.uka.ilkd.key.gui.prooftree.GUIAbstractTreeNode;
import de.uka.ilkd.key.gui.prooftree.Style;
import de.uka.ilkd.key.gui.prooftree.Styler;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.proof.event.ProofDisposedEvent;
import de.uka.ilkd.key.proof.event.ProofDisposedListener;

import org.key_project.exploration.actions.*;
import org.key_project.exploration.ui.ExplorationStepsList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Entry point for the Proof Exploration Extension.
 *
 * @author Alexander Weigl
 * @version 1 (16.04.19)
 */
@NullMarked
@KeYGuiExtension.Info(name = "Exploration",
    description = "Author: Sarah Grebing <grebing@ira.uka.de>, Alexander Weigl <weigl@ira.uka.de>",
    experimental = true, optional = true, priority = 10000)
@HelpInfo(path = "/user/Exploration/")
public class ExplorationExtension implements KeYGuiExtension, KeYGuiExtension.ContextMenu,
        KeYGuiExtension.Startup, KeYGuiExtension.Toolbar, KeYGuiExtension.MainMenu,
        KeYGuiExtension.LeftPanel, KeYGuiExtension.StatusLine, ProofDisposedListener {
    private final ExplorationModeModel model = new ExplorationModeModel();

    private @Nullable JToolBar explorationToolbar;

    private @Nullable ExplorationStepsList leftPanel;

    private final ContextMenuAdapter adapter = new ContextMenuAdapter() {
        @Override
        public <T> List<Action> getContextActions(KeYMediator mediator, ContextMenuKind<T> kind,
                T object) {
            if (!model.isExplorationModeSelected() ||
                    kind != ContextMenuKind.SEQUENT_VIEW) {
                return Collections.emptyList();
            }

            var pos = (PosInSequent) object;
            return Arrays.asList(new AddFormulaToAntecedentAction(),
                new AddFormulaToSuccedentAction(), new EditFormulaAction(pos),
                new DeleteFormulaAction(pos));
        }
    };

    private final ProofTreeListener proofTreeListener = new ProofTreeAdapter() {

        @Override
        public void proofPruned(de.uka.ilkd.key.proof.ProofTreeEvent e) {
            e.getNode().deregister(e.getNode().lookup(ExplorationNodeData.class),
                ExplorationNodeData.class);
        }
    };

    @Override
    public @NonNull List<Action> getContextActions(@NonNull KeYMediator mediator,
            @NonNull ContextMenuKind kind, @NonNull Object underlyingObject) {
        return adapter.getContextActions(mediator, kind, underlyingObject);
    }

    @Override
    public @NonNull JToolBar getToolbar(MainWindow mainWindow) {
        if (explorationToolbar == null) {
            explorationToolbar = new JToolBar();
            explorationToolbar.add(new JCheckBox(new ToggleExplorationAction(model, mainWindow)));
            explorationToolbar
                    .add(new JCheckBox(new ShowInteractiveBranchesAction(model, mainWindow)));
        }
        return explorationToolbar;
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        mediator.register(model, ExplorationModeModel.class);
        ExplorationExtension extension = this;
        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent<Node> e) {
                // ignored
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
                ExplorationStepsList panel = leftPanel();
                Proof oldProof = panel.getProof();
                Proof newProof = mediator.getSelectedProof();
                if (oldProof != newProof) {
                    panel.setProof(newProof);
                    if (oldProof != null) {
                        oldProof.removeProofTreeListener(proofTreeListener);
                    }
                    if (newProof != null) {
                        newProof.addProofTreeListener(proofTreeListener);
                        newProof.addProofDisposedListener(extension);
                    }
                }
            }
        });

        window.getProofTreeView().getRenderer().add(new ExplorationRenderer());
    }

    private @NonNull ExplorationStepsList leftPanel() {
        ExplorationStepsList panel = leftPanel;
        if (panel == null) {
            throw new NullPointerException("Exploration steps list is not initialized.");
        }
        return panel;
    }

    private @NonNull ExplorationStepsList initLeftPanel(@NonNull MainWindow window) {
        ExplorationStepsList panel = new ExplorationStepsList(window);
        leftPanel = panel;
        panel.setEnabled(model.isExplorationModeSelected());
        model.addPropertyChangeListener(ExplorationModeModel.PROP_EXPLORE_MODE,
            e -> panel.setEnabled(model.isExplorationModeSelected()));
        return panel;
    }

    @Override
    public @NonNull Collection<TabPanel> getPanels(@NonNull MainWindow window,
            @NonNull KeYMediator mediator) {
        ExplorationStepsList panel = leftPanel;
        if (panel == null) {
            panel = initLeftPanel(window);
        }

        return Collections.singleton(panel);
    }

    @Override
    public List<JComponent> getStatusLineComponents() {
        ExplorationStepsList panel = leftPanel;
        if (panel == null) {
            panel = initLeftPanel(MainWindow.getInstance());
        }

        return Collections.singletonList(panel.getHasExplorationSteps());
    }

    @Override
    public @NonNull List<Action> getMainMenuActions(@NonNull MainWindow mainWindow) {
        return Arrays.asList(new ToggleExplorationAction(model, mainWindow),
            new ShowInteractiveBranchesAction(model, mainWindow));
    }

    @Override
    public void proofDisposing(ProofDisposedEvent e) {
        ExplorationStepsList panel = leftPanel();
        if (e.getSource() == panel.getProof()) {
            panel.setProof(null);
        }
    }

    @Override
    public void proofDisposed(ProofDisposedEvent e) {

    }
}


@NullMarked
class ExplorationRenderer implements Styler<GUIAbstractTreeNode> {
    public static final ColorSettings.ColorProperty DARK_PURPLE_COLOR =
        ColorSettings.define("[proofTree]darkPurple", "", new Color(112, 17, 191));
    public static final ColorSettings.ColorProperty LIGHT_PURPLE_COLOR =
        ColorSettings.define("[proofTree]lightPurple", "", new Color(165, 146, 191));

    @Override
    public void style(@NonNull Style style, GUIAbstractTreeNode treeNode) {
        Node node = treeNode.getNode();
        if (node == null) {
            // the underlying proof node has already been garbage collected
            return;
        }
        ExplorationNodeData data = node.lookup(ExplorationNodeData.class);

        if (data != null) {
            style.border = DARK_PURPLE_COLOR.get();
            style.background = LIGHT_PURPLE_COLOR.get();
            if (style.tooltip != null) {
                style.tooltip.setTitle("Exploration Action Performed");
            }
        }
    }
}
