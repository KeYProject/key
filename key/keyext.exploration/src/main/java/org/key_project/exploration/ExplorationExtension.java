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
import de.uka.ilkd.key.gui.prooftree.GUIAbstractTreeNode;
import de.uka.ilkd.key.gui.prooftree.Style;
import de.uka.ilkd.key.gui.prooftree.Styler;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Node;
import org.key_project.exploration.actions.*;
import org.key_project.exploration.ui.ExplorationModeToolBar;
import org.key_project.exploration.ui.ExplorationStepsList;

import javax.swing.*;
import java.awt.*;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (16.04.19)
 */
@KeYGuiExtension.Info(name = "Exploration",
        description = "Author: Sarah Grebing <sgrebing@ira.uka.de>, Alexander Weigl <weigl@ira.uka.de>",
        experimental = false,
        optional = true,
        priority = 10000)
public class ExplorationExtension implements KeYGuiExtension,
        KeYGuiExtension.ContextMenu,
        KeYGuiExtension.Startup,
        KeYGuiExtension.Toolbar,
        KeYGuiExtension.LeftPanel {
    private ExplorationModeModel model = new ExplorationModeModel();

    private JToolBar explorationToolbar;

    private ExplorationStepsList leftPanel;

    private ContextMenuAdapter adapter = new ContextMenuAdapter() {
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


    @Override
    public List<Action> getContextActions(KeYMediator mediator,
                                          ContextMenuKind kind, Object underlyingObject) {
        return adapter.getContextActions(mediator, kind, underlyingObject);
    }

    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        if (explorationToolbar == null) {
            explorationToolbar = new JToolBar();
            explorationToolbar.add(new ToggleExplorationAction(model));
            explorationToolbar.add(new ShowSecondBranchAction(model));
        }
        return explorationToolbar;
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        mediator.register(model, ExplorationModeModel.class);
        mediator.addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent e) {
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent e) {
                leftPanel.setProof(mediator.getSelectedProof());
            }
        });


        window.getProofTreeView().getRenderer().add(new ExplorationRenderer());

    }

    @Override
    public Collection<TabPanel> getPanels(MainWindow window, KeYMediator mediator) {
        if (leftPanel == null) leftPanel = new ExplorationStepsList(window);
        return Collections.singleton(leftPanel);
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
    public void style(Style style, GUIAbstractTreeNode treeNode) {
        Node node = treeNode.getNode();
        ExplorationNodeData data = null;
        try {
            data = node.getNodeInfo().get(ExplorationNodeData.class);

            if (data != null) {
                style.setBorder(DARK_PURPLE_COLOR.get());
                style.setBackground(LIGHT_PURPLE_COLOR.get());
                style.setTooltip("Exploration Action Performed");

            } else {
                style.setBorder(null);
            }
        } catch (IllegalStateException e){
            style.setBorder(null);
        }
    }
}
