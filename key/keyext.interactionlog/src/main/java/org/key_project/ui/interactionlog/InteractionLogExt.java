package org.key_project.ui.interactionlog;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.extension.api.TabPanel;

import javax.swing.*;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (13.02.19)
 */
@KeYGuiExtension.Info(name = "Interaction Logging",
        optional = true,
        experimental = false,
        description = "Recording of all proof manipulation interactions",
        priority = 10000)
public class InteractionLogExt implements KeYGuiExtension, KeYGuiExtension.LeftPanel, KeYGuiExtension.MainMenu {
    private InteractionLogView interactionLogView;


    @Override
    public List<Action> getMainMenuActions(MainWindow mainWindow) {
        InteractionLogView ilv = getView(mainWindow);

        return Arrays.asList(
                ilv.getActionAddUserNote(),
                ilv.getActionExportProofScript(),
                ilv.getActionJumpIntoTree(),
                ilv.getActionLoad(),
                ilv.getActionSave(),
                ilv.getActionTryReapply(),
                ilv.getActionKPSExport(),
                ilv.getActionToggleFavourite(),
                ilv.getActionExportMarkdown(),
                ilv.getActionMUCopyClipboard(),
                ilv.getActionPauseLogging());
    }

    private InteractionLogView getView(MainWindow mainWindow) {
        if (interactionLogView == null)
            interactionLogView = new InteractionLogView(mainWindow, mainWindow.getMediator());
        return interactionLogView;
    }

    @Override
    public Collection<TabPanel> getPanels(MainWindow window, KeYMediator mediator) {
        return Collections.singleton(getView(window));
    }
}
