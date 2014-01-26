package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.prooftree.ProofTreeView;
import de.uka.ilkd.key.util.GuiUtilities;
import java.awt.Toolkit;
import java.awt.event.KeyEvent;
import javax.swing.JComponent;
import javax.swing.JScrollPane;
import javax.swing.JTabbedPane;
import javax.swing.KeyStroke;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class MainWindowTabbedPane extends JTabbedPane {

    /**
     * the current proof tree
     */
    private ProofTreeView proofTreeView;

    public ProofTreeView getProofTreeView() {
        return proofTreeView;
    }

    /**
     * the list of current open goals
     */
    private JScrollPane openGoalsView;

    /**
     * the strategy selection view
     */
    private StrategySelectionView strategySelectionView = null;

    /**
     * the rule view
     */
    private RuleView ruleView = null;

    MainWindowTabbedPane() {
        addTab("Proof", null, proofTreeView,
                "The current state of the proof as tree");
        addTab("Goals", null, openGoalsView,
                "The currently open goals");
        addTab("Proof Search Strategy", null, strategySelectionView,
                "Select strategy for automated proof search");
        addTab("Rules", null, ruleView,
                "All available rules");

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
        ruleView.setEnabled(b);
    }

    protected void createViews(MainWindow mainWindow, KeYMediator mediator) {
        openGoalsView = new JScrollPane();
        GuiUtilities.paintEmptyViewComponent(openGoalsView, "Open Goals");

        strategySelectionView = new StrategySelectionView(mainWindow);
        if (mediator != null) {
            strategySelectionView.setMediator(mediator);
        }

        ruleView = new RuleView();
        if (mediator != null) {
            ruleView.setMediator(mediator);
        }

        Config.DEFAULT.setDefaultFonts();
    }

    /**
     * create the goal list, proof tree, proof list. Add to their respective
     * containers.
     */
    protected void createProofElements(KeYMediator mediator) {
        proofTreeView = new ProofTreeView(mediator);
        proofTreeView.setSize(proofTreeView.getPreferredSize());
        proofTreeView.setVisible(true);

        GoalList goalList = new GoalList(mediator);
        // FIXME IS that needed?
        goalList.setSize(goalList.getPreferredSize());
        openGoalsView.setViewportView(goalList);
    }

}
