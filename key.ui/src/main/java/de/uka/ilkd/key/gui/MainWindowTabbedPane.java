/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.KeyEvent;
import java.util.stream.Stream;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.actions.AutoModeAction;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.prooftree.ProofTreeView;

/**
 * {@link JTabbedPane} displayed in {@link MainWindow}, to the left of
 * {@link de.uka.ilkd.key.gui.nodeviews.SequentView}.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
@Deprecated
public class MainWindowTabbedPane extends JTabbedPane {
    private static final long serialVersionUID = 1L;
    public static final float TAB_ICON_SIZE = 16f;
    private final ProofTreeView proofTreeView;

    MainWindowTabbedPane(MainWindow mainWindow, KeYMediator mediator,
            AutoModeAction autoModeAction) {
        assert mediator != null;
        assert mainWindow != null;

        proofTreeView = new ProofTreeView(mediator);
        InfoView infoView = new InfoView(mainWindow, mediator);
        StrategySelectionView strategySelectionView =
            new StrategySelectionView(mainWindow, mediator);
        GoalList openGoalsView = new GoalList(mediator);

        Stream<TabPanel> panels = KeYGuiExtensionFacade.getAllPanels(mainWindow);
        addPanel(infoView);
        addPanel(strategySelectionView);
        addPanel(openGoalsView);
        addPanel(proofTreeView);
        panels.forEach(this::addPanel);


        // change some key mappings which collide with font settings.
        getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT).getParent()
                .remove(KeyStroke.getKeyStroke(KeyEvent.VK_UP,
                    Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        getInputMap(JComponent.WHEN_FOCUSED).getParent().remove(KeyStroke.getKeyStroke(
            KeyEvent.VK_DOWN, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
        setName("leftTabbed");
    }

    protected void addPanel(TabPanel p) {
        addTab(p.getTitle(), p.getIcon(), p.getComponent());
    }

    protected void setEnabledForAllTabs(boolean b) {
        for (int i = 0; i < getTabCount(); i++) {
            getComponentAt(i).setEnabled(b);
        }
    }

    public ProofTreeView getProofTreeView() {
        return proofTreeView;
    }
}
