package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.actions.AutoModeAction;
import de.uka.ilkd.key.gui.ext.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.ext.KeYPaneExtension;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeBold;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;
import de.uka.ilkd.key.gui.interactionlog.InteractionLogView;
import de.uka.ilkd.key.gui.prooftree.ProofTreeView;

import javax.swing.*;
import java.awt.*;
import java.awt.event.KeyEvent;
import java.util.List;

/**
 * {@link JTabbedPane} displayed in {@link MainWindow}, to the left of
 * {@link de.uka.ilkd.key.gui.nodeviews.SequentView}.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class MainWindowTabbedPane extends JTabbedPane {
    public static final float TAB_ICON_SIZE = 16f;

    /**
     * the current proof tree
     */
    private ProofTreeView proofTreeView;

    MainWindowTabbedPane(MainWindow mainWindow, KeYMediator mediator, AutoModeAction autoModeAction) {
        assert mediator != null;
        assert mainWindow != null;

        proofTreeView = KeYGuiExtensionFacade.getPanel(ProofTreeView.class).orElse(null);
        //infoView = KeYGuiExtensionFacade.getPanel(InfoView.class).orElse(null);
        //strategySelectionView = KeYGuiExtensionFacade.getPanel(StrategySelectionView.class).orElse(null);
        //openGoalsView = KeYGuiExtensionFacade.getPanel(GoalList.class).orElse(null);

        List<KeYPaneExtension> panels = KeYGuiExtensionFacade.getAllPanels();
        panels.forEach(p -> p.init(mainWindow, mediator));
        panels.forEach(p -> addTab(p.getTitle(), p.getIcon(), p.getComponent()));


        // change some key mappings which collide with font settings.
        getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT)
                .getParent().remove(
                KeyStroke.getKeyStroke(KeyEvent.VK_UP, Toolkit
                        .getDefaultToolkit().getMenuShortcutKeyMask()));
        getInputMap(JComponent.WHEN_FOCUSED).getParent().remove(
                KeyStroke.getKeyStroke(KeyEvent.VK_DOWN, Toolkit
                        .getDefaultToolkit().getMenuShortcutKeyMask()));
        setName("leftTabbed");
    }

    protected void setEnabledForAllTabs(boolean b) {
        for(int i = 0; i < getTabCount(); i++)
            getComponentAt(i).setEnabled(b);
    }

    public ProofTreeView getProofTreeView() {
        return proofTreeView;
    }
}
