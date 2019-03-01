package de.uka.ilkd.key.gui.interactionlog;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.MainWindowTabbedPane;
import de.uka.ilkd.key.gui.ext.KeYMainMenuExtension;
import de.uka.ilkd.key.gui.ext.KeYPaneExtension;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeBold;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;

import javax.swing.*;
import java.util.Arrays;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (13.02.19)
 */
public class InteractionLogExt implements KeYPaneExtension, KeYMainMenuExtension {
    private static final Icon INTERACTION_LOG_ICON = IconFontSwing.buildIcon(FontAwesomeBold.BOOK,
            MainWindowTabbedPane.TAB_ICON_SIZE);

    private InteractionLogView interactionLogView = new InteractionLogView();

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        interactionLogView.setMediator(mediator);
        interactionLogView.setMainWindow(window);
    }

    @Override
    public String getTitle() {
        return "Interaction Log";
    }

    @Override
    public Icon getIcon() {
        return INTERACTION_LOG_ICON;
    }

    @Override
    public JComponent getComponent() {
        return interactionLogView;
    }

    @Override
    public int priority() {
        return 1500;
    }

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
}
