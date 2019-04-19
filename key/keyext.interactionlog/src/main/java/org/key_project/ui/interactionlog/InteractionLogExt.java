package org.key_project.ui.interactionlog;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.fonticons.KeYIcons;

import javax.swing.*;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (13.02.19)
 */
@KeYGuiExtension.Info(name = "Interaction Logging", optional = true, priority = 10000)
public class InteractionLogExt implements KeYGuiExtension, KeYGuiExtension.LeftPanel, KeYGuiExtension.MainMenu {

    private InteractionLogView interactionLogView;


    @Override
    public List<Action> getMainMenuActions(MainWindow mainWindow) {
        return Arrays.asList(
                interactionLogView.getActionAddUserNote(),
                interactionLogView.getActionExportProofScript(),
                interactionLogView.getActionJumpIntoTree(),
                interactionLogView.getActionLoad(),
                interactionLogView.getActionSave(),
                interactionLogView.getActionTryReapply(),
                interactionLogView.getActionKPSExport(),
                interactionLogView.getActionToggleFavourite(),
                interactionLogView.getActionExportMarkdown(),
                interactionLogView.getActionMUCopyClipboard(),
                interactionLogView.getActionPauseLogging());
    }

    @Override
    public Collection<TabPanel> getPanels(MainWindow window, KeYMediator mediator) {
        interactionLogView = new InteractionLogView(window, mediator);
        return Collections.singleton(interactionLogView);
    }
}
