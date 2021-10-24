package org.key_project.exploration;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.colors.ColorSettings;
import de.uka.ilkd.key.gui.extension.api.ContextMenuAdapter;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.prooftree.*;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Node;
import org.key_project.exploration.actions.*;
import org.key_project.exploration.ui.ExplorationStepsList;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.*;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

/**
 * Entry point for the Proof Exploration Extension.
 * @author Alexander Weigl
 * @version 1 (16.04.19)
 */
@KeYGuiExtension.Info(name = "Exploration",
        description = "Author: Sarah Grebing <grebing@ira.uka.de>, Alexander Weigl <weigl@ira.uka.de>",
        experimental = false,
        optional = true,
        priority = 10000)
public class ExplorationExtension implements KeYGuiExtension,
        KeYGuiExtension.ContextMenu,
        KeYGuiExtension.Startup,
        KeYGuiExtension.Toolbar,
        KeYGuiExtension.MainMenu,
        KeYGuiExtension.LeftPanel, KeYGuiExtension.StatusLine {
    private final ExplorationModeModel model = new ExplorationModeModel();

    private JToolBar explorationToolbar;

    private ExplorationStepsList leftPanel;

    private final ContextMenuAdapter adapter = new ContextMenuAdapter() {
        @Override
        public List<Action> getContextActions(KeYMediator mediator, ContextMenuKind kind, PosInSequent pos) {
            if (model.isExplorationModeSelected()) {
                return Arrays.asList(new AddFormulaToAntecedentAction(),
                        new AddFormulaToSuccedentAction(),
                        new EditFormulaAction(pos),
                        new DeleteFormulaAction(pos));
            }
            return super.getContextActions(mediator, kind, pos);
        }
    };


    @Nonnull
    @Override
    public List<Action> getContextActions(@Nonnull KeYMediator mediator,
                                          @Nonnull ContextMenuKind kind,
                                          @Nonnull Object underlyingObject) {
        return adapter.getContextActions(mediator, kind, underlyingObject);
    }

    @Nonnull
    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        if (explorationToolbar == null) {
            explorationToolbar = new JToolBar();
            explorationToolbar.add(new JToggleButton(new ToggleExplorationAction(model)));
            explorationToolbar.add(new JToggleButton(new ShowSecondBranchAction(model)));
        }
        return explorationToolbar;
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        mediator.register(model, ExplorationModeModel.class);
        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
                // ignored
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                leftPanel.setProof(mediator.getSelectedProof());
            }
        });

        model.addPropertyChangeListener(ExplorationModeModel.PROP_SHOW_SECOND_BRANCH,
                e -> {
                    GUIProofTreeModel delegateModel =
                            window.getProofTreeView().getDelegateModel();

                    delegateModel.setFilter(ProofTreeViewFilter.HIDE_INTERACTIVE_GOALS,
                            !model.isShowSecondBranches());
                });
        window.getProofTreeView().getRenderer().add(new ExplorationRenderer());


    }

    @Nonnull
    @Override
    public Collection<TabPanel> getPanels(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        if (leftPanel == null) leftPanel = new ExplorationStepsList(window);
        return Collections.singleton(leftPanel);
    }

    @Override
    public List<JComponent> getStatusLineComponents() {
        if (leftPanel == null) leftPanel = new ExplorationStepsList(MainWindow.getInstance());
        return Collections.singletonList(leftPanel.getHasExplorationSteps());
    }

    @Override
    public @Nonnull List<Action> getMainMenuActions(@Nonnull MainWindow mainWindow) {
        return Arrays.asList(
                new ToggleExplorationAction(model),
                new ShowSecondBranchAction(model));
    }
}

class ExplorationRenderer implements Styler<GUIAbstractTreeNode> {
    public static final ColorSettings.ColorProperty DARK_TURQOUIS_COLOR =
            ColorSettings.define("[proofTree]turqois", "", new Color(19, 110, 128));
    public static final ColorSettings.ColorProperty DARK_PURPLE_COLOR =
            ColorSettings.define("[proofTree]darkPurple", "", new Color(112, 17, 191));
    public static final ColorSettings.ColorProperty LIGHT_PURPLE_COLOR =
            ColorSettings.define("[proofTree]lightPurple", "", new Color(165, 146, 191));

    @Override
    public void style(@Nonnull Style style, GUIAbstractTreeNode treeNode) {
        Node node = treeNode.getNode();
        ExplorationNodeData data;
        try {
            data = node.lookup(ExplorationNodeData.class);

            if (data != null) {
                style.set(Style.KEY_COLOR_BORDER, DARK_PURPLE_COLOR.get());
                style.set(Style.KEY_COLOR_BACKGROUND, LIGHT_PURPLE_COLOR.get());
                style.set(Style.KEY_TOOLTIP, "Exploration Action Performed");

            } else {
                style.set(Style.KEY_COLOR_BORDER, null);
            }
        } catch (IllegalStateException e) {
            style.set(Style.KEY_COLOR_BORDER, null);
        }
    }
}
