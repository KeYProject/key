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

    private static final long serialVersionUID = 334677113533050832L;


    /**
     * the current proof tree
     */
    private ProofTreeView proofTreeView;
    private InteractionLogView interactionLogView;
    /**
     * the list of current open goals
     */
    private GoalList openGoalsView;

    /**
     * the strategy selection view
     */
    private StrategySelectionView strategySelectionView;

    /**
     * the rule view
     */
    private InfoView infoView;

    MainWindowTabbedPane(MainWindow mainWindow, KeYMediator mediator, AutoModeAction autoModeAction) {
        assert mediator != null;
        assert mainWindow != null;

        proofTreeView = KeYGuiExtensionFacade.getPanel(ProofTreeView.class).orElse(null);
        infoView = KeYGuiExtensionFacade.getPanel(InfoView.class).orElse(null);
        strategySelectionView = KeYGuiExtensionFacade.getPanel(StrategySelectionView.class).orElse(null);
        openGoalsView = KeYGuiExtensionFacade.getPanel(GoalList.class).orElse(null);
        List<KeYPaneExtension> panels = KeYGuiExtensionFacade.getAllPanels();
        panels.forEach(p -> p.init(mainWindow, mediator));
        panels.forEach(p -> addTab(p.getTitle(), p.getIcon(), p.getComponent()));


        // set proofTreeView
        /*
        proofTreeView = new ProofTreeView(mediator);
        proofTreeView.setSize(proofTreeView.getPreferredSize());
        proofTreeView.setVisible(true);
        addTab("Proof", PROOF_ICON, proofTreeView,
                "The current state of the proof as tree");

        // set openGoalsView
        openGoalsView = new JScrollPane();
        GuiUtilities.paintEmptyViewComponent(openGoalsView, "Open Goals");
        GoalList goalList = new GoalList(mediator);
        // FIXME IS that needed?
        goalList.setSize(goalList.getPreferredSize());
        openGoalsView.setViewportView(goalList);
        addTab("Goals", null, openGoalsView,
                "The currently open goals");

        // set strategySelectionView
        strategySelectionView = new StrategySelectionView(autoModeAction);
        strategySelectionView.setMediator(mediator);
        addTab("Proof Search Strategy", PROOF_SEARCH_STRATEGY_ICON, strategySelectionView,
                "Select strategy for automated proof search");

        // set ruleView
        infoView = new InfoView(mediator, mainWindow);
        addTab("Info", INFO_ICON, infoView,
                "Documentation on taclets and symbols");

        setSelectedIndex(0);
        setPreferredSize(new java.awt.Dimension(250, 440));
           */

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
        proofTreeView.setEnabled(b);
        openGoalsView.setEnabled(b);
        strategySelectionView.setEnabled(b);
        infoView.setEnabled(b);
    }

    public ProofTreeView getProofTreeView() {
        return proofTreeView;
    }
}
