package de.uka.ilkd.key.gui.docking;

import java.util.LinkedList;
import java.util.List;
import java.util.stream.Stream;

import javax.swing.Action;
import javax.swing.Icon;
import javax.swing.JComponent;

import org.jetbrains.annotations.NotNull;

import bibliothek.gui.dock.common.CGrid;
import bibliothek.gui.dock.common.DefaultSingleCDockable;
import bibliothek.gui.dock.common.MultipleCDockable;
import bibliothek.gui.dock.common.SingleCDockable;
import bibliothek.gui.dock.common.action.CAction;
import bibliothek.gui.dock.common.action.CButton;
import bibliothek.gui.dock.common.action.CCheckBox;
import bibliothek.gui.dock.common.intern.CDockable;
import de.uka.ilkd.key.gui.GoalList;
import de.uka.ilkd.key.gui.InfoView;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.StrategySelectionView;
import de.uka.ilkd.key.gui.TaskTree;
import de.uka.ilkd.key.gui.extension.api.TabPanel;
import de.uka.ilkd.key.gui.nodeviews.MainFrame;
import de.uka.ilkd.key.gui.prooftree.ProofTreeView;
import de.uka.ilkd.key.gui.sourceview.SourceViewFrame;

public class DockingHelper {
    public final static List<String> LEFT_TOP_PANEL = new LinkedList<>();
    public final static List<String> RIGHT_PANEL = new LinkedList<>();
    public final static List<String> LEFT_PANEL = new LinkedList<>();
    public final static List<String> MAIN_PANEL = new LinkedList<>();

    static {
        LEFT_TOP_PANEL.add(TaskTree.class.getName());

        LEFT_PANEL.add(GoalList.class.getName());
        LEFT_PANEL.add(ProofTreeView.class.getName());
        LEFT_PANEL.add(InfoView.class.getName());
        LEFT_PANEL.add(StrategySelectionView.class.getName());

        MAIN_PANEL.add(MainFrame.class.getName());

        RIGHT_PANEL.add(SourceViewFrame.class.getName());
    }

    /**
     * Sets the current layout of the docking framework back to factory default.
     * <p>
     * We distinguish between four areas: left-top, left(-bottom), main, right.
     * This methods goes through all dockables, and attach them to one of these areas,
     * according to static fields above. The <code>id</code> field is used for identification,
     * which is currently determined by the class name.
     *
     * @param mainWindow
     * @see #LEFT_PANEL
     * @see #LEFT_TOP_PANEL
     * @see #MAIN_PANEL
     * @see #RIGHT_PANEL
     * @see #createSingleDock(String, JComponent)
     * @see #createSingleDock(TabPanel)
     */
    public static void restoreFactoryDefault(MainWindow mainWindow) {
        List<CDockable>
                leftPanels = new LinkedList<>(),
                leftTopPanels = new LinkedList<>(),
                mainPanels = new LinkedList<>(),
                rightPanels = new LinkedList<>();

        for (int c = mainWindow.getDockControl().getCDockableCount(), i = 0;
             i < c; i++) {
            final CDockable cur = mainWindow.getDockControl().getCDockable(i);
            if (cur instanceof SingleCDockable) {
                final String id = ((SingleCDockable) cur).getUniqueId();
                if (LEFT_PANEL.contains(id)) {
                    leftPanels.add(cur);
                    continue;
                }
                if (MAIN_PANEL.contains(id)) {
                    mainPanels.add(cur);
                    continue;
                }
                if (RIGHT_PANEL.contains(id)) {
                    rightPanels.add(cur);
                    continue;
                }
                if (LEFT_TOP_PANEL.contains(id)) {
                    leftTopPanels.add(cur);
                    continue;
                }
            }

            if (cur instanceof MultipleCDockable) {
                mainPanels.add(cur);
                continue;
            }
            leftPanels.add(cur);
        }

        CGrid grid = new CGrid(mainWindow.getDockControl());
        grid.add(0, 0, 1, 1, leftTopPanels.toArray(new CDockable[]{}));
        grid.add(0, 1, 1, 2, leftPanels.toArray(new CDockable[]{}));
        grid.add(1, 0, 2, 3, mainPanels.toArray(new CDockable[]{}));
        grid.add(2, 0, 1, 3, rightPanels.toArray(new CDockable[]{}));
        mainWindow.getDockControl().getContentArea().deploy(grid);
    }


    /**
     * Constructs a dockable for the given component.
     *
     * @param title     a non-null, non-empty title for this dock
     * @param component a non-null component to show
     * @return a {@link DefaultSingleCDockable}
     * @see #createSingleDock(TabPanel)
     */
    public static SingleCDockable createSingleDock(String title, JComponent component) {
        return createSingleDock(title, component, component.getClass().getName());
    }

    public static SingleCDockable createSingleDock(String title, JComponent component, String id) {
        return new DefaultSingleCDockable(id, title, component);
    }

    /**
     * @param p
     * @return
     */
    public static SingleCDockable createSingleDock(TabPanel p) {
        Stream<CAction> actions = p.getTitleActions().stream().map(DockingHelper::translateAction);
        CAction[] a = Stream.concat(actions, p.getTitleCActions().stream()).toArray(CAction[]::new);

        return new DefaultSingleCDockable(p.getClass().getName(),
                p.getIcon(), p.getTitle(), p.getComponent(),
                p.getPermissions(), a);
    }

    public static @NotNull CAction translateAction(@NotNull Action action) {
        if (action.getValue(Action.SELECTED_KEY) != null) {
            return createCheckBox(action);

        } else {
            return createButton(action);
        }
    }

    private static @NotNull CAction createCheckBox(@NotNull Action action) {
        CCheckBox button = new CCheckBox(
                (String) action.getValue(Action.NAME),
                (Icon) action.getValue(Action.SMALL_ICON)) {
            @Override
            protected void changed() {
                action.putValue(Action.SELECTED_KEY, this.isSelected());
                action.actionPerformed(null);
            }
        };

        button.setTooltip((String) action.getValue(Action.SHORT_DESCRIPTION));
        button.setEnabled(action.isEnabled());
        button.setSelected(Boolean.TRUE == action.getValue(Action.SELECTED_KEY));
        action.addPropertyChangeListener(evt -> {
            button.setText((String) action.getValue(Action.NAME));
            button.setIcon((Icon) action.getValue(Action.SMALL_ICON));
            button.setTooltip((String) action.getValue(Action.SHORT_DESCRIPTION));
            button.setEnabled(action.isEnabled());
        });
        return button;
    }

    private static CAction createButton(Action action) {
        CButton button = new CButton(
                (String) action.getValue(Action.NAME),
                (Icon) action.getValue(Action.SMALL_ICON));
        button.addActionListener(action);
        button.setTooltip((String) action.getValue(Action.SHORT_DESCRIPTION));
        button.setEnabled(action.isEnabled());

        action.addPropertyChangeListener(evt -> {
            button.setText((String) action.getValue(Action.NAME));
            button.setIcon((Icon) action.getValue(Action.SMALL_ICON));
            button.setTooltip((String) action.getValue(Action.SHORT_DESCRIPTION));
            button.setEnabled(action.isEnabled());
        });

        return button;
    }
}
