package org.key_project.exploration;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.ContextMenuAdapter;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.pp.PosInSequent;
import org.key_project.exploration.actions.AddFormulaToAntecedentAction;
import org.key_project.exploration.actions.AddFormulaToSuccedentAction;
import org.key_project.exploration.actions.DeleteFormulaAction;
import org.key_project.exploration.actions.EditFormulaAction;
import org.key_project.exploration.ui.ExplorationModeToolBar;
import org.key_project.exploration.ui.ExplorationStepsList;

import javax.swing.*;
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
    private JToolBar explorationToolbar;
    private ExplorationModeModel model = new ExplorationModeModel();
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
    private ExplorationStepsList leftPanel;

    @Override
    public List<Action> getContextActions(KeYMediator mediator,
                                          ContextMenuKind kind, Object underlyingObject) {
        return adapter.getContextActions(mediator, kind, underlyingObject);
    }

    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        if (explorationToolbar == null) {
            explorationToolbar = new ExplorationModeToolBar(mainWindow, model);
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
    }

    @Override
    public Collection<TabPanel> getPanels(MainWindow window, KeYMediator mediator) {
        if (leftPanel == null) leftPanel = new ExplorationStepsList(window);
        return Collections.singleton(leftPanel);
    }
}
