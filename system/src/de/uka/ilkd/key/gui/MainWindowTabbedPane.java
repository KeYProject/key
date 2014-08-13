package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.gui.actions.AutoModeAction;
import de.uka.ilkd.key.gui.prooftree.ProofTreeView;
import de.uka.ilkd.key.util.GuiUtilities;
import java.awt.Toolkit;
import java.awt.event.KeyEvent;
import javax.swing.JComponent;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.KeyStroke;

/**
 * {@link JTabbedPane} displayed in {@link MainWindow}, to the left of
 * {@link de.uka.ilkd.key.gui.nodeviews.SequentView}.
 * 
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class MainWindowTabbedPane extends JTabbedPane {

    /**
     *
     */
    private static final long serialVersionUID = 334677113533050832L;

    /**
     * the current proof tree
     */
    private final ProofTreeView proofTreeView;

    public ProofTreeView getProofTreeView() {
        return proofTreeView;
    }

    /**
     * the list of current open goals
     */
    private final JScrollPane openGoalsView;

    /**
     * the strategy selection view
     */
    private final StrategySelectionView strategySelectionView;

    /**
     * the rule view
     */
    private final InfoView infoView;

    MainWindowTabbedPane(MainWindow mainWindow, KeYMediator mediator, AutoModeAction autoModeAction) {
        assert mediator != null;
        assert mainWindow != null;

        // set proofTreeView
        proofTreeView = new ProofTreeView(mediator);
        proofTreeView.setSize(proofTreeView.getPreferredSize());
        proofTreeView.setVisible(true);
        addTab("Proof", null, proofTreeView,
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
        addTab("Proof Search Strategy", null, strategySelectionView,
                "Select strategy for automated proof search");

        // set ruleView
        infoView = new InfoView(mediator, mainWindow);
        addTab("Info", null, infoView,
                "Documentation on taclets and symbols");

        setSelectedIndex(0);
        setPreferredSize(new java.awt.Dimension(250, 440));

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

}
