/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.exploration;

import java.awt.*;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import javax.annotation.Nonnull;
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

/**
 * Entry point for the Proof Exploration Extension.
 *
 * @author Alexander Weigl
 * @version 1 (16.04.19)
 */
@KeYGuiExtension.Info(name = "Exploration",
    description = "Author: Sarah Grebing <grebing@ira.uka.de>, Alexander Weigl <weigl@ira.uka.de>",
    experimental = true, optional = true, priority = 10000)
public class ExplorationExtension implements KeYGuiExtension, KeYGuiExtension.ContextMenu,
        KeYGuiExtension.Startup, KeYGuiExtension.Toolbar, KeYGuiExtension.MainMenu,
        KeYGuiExtension.LeftPanel, KeYGuiExtension.StatusLine, ProofDisposedListener {
    private final ExplorationModeModel model = new ExplorationModeModel();

    private JToolBar explorationToolbar;

    private ExplorationStepsList leftPanel;

    private final ContextMenuAdapter adapter = new ContextMenuAdapter() {
        @Override
        public List<Action> getContextActions(KeYMediator mediator, ContextMenuKind kind,
                PosInSequent pos) {
            if (model.isExplorationModeSelected()) {
                return Arrays.asList(new AddFormulaToAntecedentAction(),
                    new AddFormulaToSuccedentAction(), new EditFormulaAction(pos),
                    new DeleteFormulaAction(pos));
            }
            return super.getContextActions(mediator, kind, pos);
        }
    };

    private final ProofTreeListener proofTreeListener = new ProofTreeAdapter() {

        public void proofPruned(de.uka.ilkd.key.proof.ProofTreeEvent e) {
            e.getNode().deregister(e.getNode().lookup(ExplorationNodeData.class),
                ExplorationNodeData.class);
        }
    };

    @Nonnull
    @Override
    public List<Action> getContextActions(@Nonnull KeYMediator mediator,
            @Nonnull ContextMenuKind kind, @Nonnull Object underlyingObject) {
        return adapter.getContextActions(mediator, kind, underlyingObject);
    }

    @Nonnull
    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
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
            public void selectedNodeChanged(KeYSelectionEvent e) {
                // ignored
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                Proof oldProof = leftPanel.getProof();
                Proof newProof = mediator.getSelectedProof();
                if (oldProof != newProof) {
                    leftPanel.setProof(newProof);
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

    private void initLeftPanel(@Nonnull MainWindow window) {
        leftPanel = new ExplorationStepsList(window);
        leftPanel.setEnabled(model.isExplorationModeSelected());
        model.addPropertyChangeListener(ExplorationModeModel.PROP_EXPLORE_MODE,
            e -> leftPanel.setEnabled(model.isExplorationModeSelected()));
    }

    @Nonnull
    @Override
    public Collection<TabPanel> getPanels(@Nonnull MainWindow window,
            @Nonnull KeYMediator mediator) {
        if (leftPanel == null) {
            initLeftPanel(window);
        }

        return Collections.singleton(leftPanel);
    }

    @Override
    public List<JComponent> getStatusLineComponents() {
        if (leftPanel == null) {
            initLeftPanel(MainWindow.getInstance());
        }

        return Collections.singletonList(leftPanel.getHasExplorationSteps());
    }

    @Override
    public @Nonnull List<Action> getMainMenuActions(@Nonnull MainWindow mainWindow) {
        return Arrays.asList(new ToggleExplorationAction(model, mainWindow),
            new ShowInteractiveBranchesAction(model, mainWindow));
    }

    @Override
    public void proofDisposing(ProofDisposedEvent e) {
        if (e.getSource() == leftPanel.getProof()) {
            leftPanel.setProof(null);
        }
    }

    @Override
    public void proofDisposed(ProofDisposedEvent e) {

    }
}


class ExplorationRenderer implements Styler<GUIAbstractTreeNode> {
    public static final ColorSettings.ColorProperty DARK_PURPLE_COLOR =
        ColorSettings.define("[proofTree]darkPurple", "", new Color(112, 17, 191));
    public static final ColorSettings.ColorProperty LIGHT_PURPLE_COLOR =
        ColorSettings.define("[proofTree]lightPurple", "", new Color(165, 146, 191));

    @Override
    public void style(@Nonnull Style style, GUIAbstractTreeNode treeNode) {
        Node node = treeNode.getNode();
        ExplorationNodeData data = node.lookup(ExplorationNodeData.class);

        if (data != null) {
            style.border = DARK_PURPLE_COLOR.get();
            style.background = LIGHT_PURPLE_COLOR.get();
            style.tooltip.setTitle("Exploration Action Performed");
        }
    }
}
