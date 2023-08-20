/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.extension.api;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.util.Collection;
import java.util.List;
import javax.annotation.Nonnull;
import javax.swing.Action;
import javax.swing.JComponent;
import javax.swing.JMenu;
import javax.swing.JToolBar;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.GoalList;
import de.uka.ilkd.key.gui.InfoView;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.StrategySelectionView;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.gui.prooftree.ProofTreeView;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.pp.PosInSequent;

/**
 * A marker interface for extension of the KeY GUI. Every extension should implement this interface
 * and should be registered in a service loader file <code>META-INF/services/KeYGuiExtension</code>.
 * <p>
 * This interface comes in combination with the annotation {@see KeYGuiExtension#Info}
 * <p>
 * Your extension should then implement the extension service interfaces.
 * </p>
 *
 * @author Alexander Weigl
 * @version 1 (07.04.19)
 */
public interface KeYGuiExtension {
    @Retention(RetentionPolicy.RUNTIME)
    @interface Info {
        /**
         * Simple name of this extension, else the fqdn of the class is used
         *
         * @return non-null string
         */
        String name() default "";

        /**
         * Optional extension can be disabled by the user.
         *
         * @return a boolean
         */
        boolean optional() default false;

        /**
         * Disabled extension are not instantiated
         *
         * @return a boolean
         */
        boolean disabled() default false;

        /**
         * Long description of this extension.
         * <p>
         * what does it? who develops it?
         *
         * @return a string, default empty
         */
        String description() default "";

        /**
         * Loading priority of this extension. Baseline is zero
         *
         * @return
         */
        int priority() default 0;

        /**
         * Marks an extensions as experimental.
         * <p>
         * Experimental extensions are only available if the KeY is started with the experimental
         * flag on the command line <code>--experimental</code>.
         */
        boolean experimental() default true;
    }

    /**
     * Main Menu extension provides entry to the extension {@link JMenu} in the main frame.
     */
    interface MainMenu {
        /**
         * A list of actions which should be added to the main menu.
         * <p>
         * Actions should use the {@link de.uka.ilkd.key.gui.actions.KeyAction#PATH} and
         * {@link de.uka.ilkd.key.gui.actions.KeyAction#PRIORITY} to control their position in the
         * menu.
         *
         * @param mainWindow the window of the main menu
         * @return non-null, emptiable list of actions.
         * @see de.uka.ilkd.key.gui.actions.KeyAction
         */
        @Nonnull
        List<Action> getMainMenuActions(@Nonnull MainWindow mainWindow);
    }

    /**
     * Simplest extension point. Called during after the initialization of the {@link MainWindow}.
     * Can be used for registering key binding.
     */
    interface Startup {
        /**
         * Earliest initialization method. Called before layout of the main window.
         *
         * @param window main window
         * @param mediator mediator
         */
        default void preInit(MainWindow window, KeYMediator mediator) {

        }

        void init(MainWindow window, KeYMediator mediator);
    }

    /**
     * This interface describes the UI extension point on the left bottom corner (JTabbedPane).
     *
     * @author Alexander Weigl
     * @version 2 (19.04.19)
     */
    interface LeftPanel {
        /**
         * Initialization and return of the sub components.
         * <p>
         * Called before any other method; can be used to construct the UI.
         *
         * @param window parent of this extension
         * @param mediator the current mediator
         */
        @Nonnull
        Collection<TabPanel> getPanels(@Nonnull MainWindow window, @Nonnull KeYMediator mediator);
    }

    /**
     * This interface describes the UI extension for adding various context menus.
     *
     * @author Alexander Weigl
     * @version 1 (07.02.19)
     */
    interface ContextMenu {
        /**
         * A list of actions which should be added to the main menu.
         * <p>
         * Actions should use the {@link de.uka.ilkd.key.gui.actions.KeyAction#PATH} and
         * {@link de.uka.ilkd.key.gui.actions.KeyAction#PRIORITY} to control their position in the
         * menu.
         *
         * @param mediator the window of the main menu
         * @param kind the type of context menu
         * @param underlyingObject the object for which the context menu is requested
         * @return non-null, emptiable list of actions.
         * @see de.uka.ilkd.key.gui.actions.KeyAction
         */
        @Nonnull
        List<Action> getContextActions(@Nonnull KeYMediator mediator, @Nonnull ContextMenuKind kind,
                @Nonnull Object underlyingObject);
    }

    /**
     * This interface describes the UI extension to add a {@link Toolbar} into the main window.
     *
     * @author Alexander Weigl
     */
    interface Toolbar {
        /**
         * A toolbar which will be embedded into the main window.s
         *
         * @param mainWindow the parent of the toolbar
         * @return non-null
         */
        @Nonnull
        JToolBar getToolbar(MainWindow mainWindow);
    }

    /**
     * Extension interface for the tooltips in the sequent view.
     *
     * @author lanzinger
     *
     * @see SequentView
     */
    interface Tooltip {

        /**
         *
         * @param mainWindow the main window.
         * @param pos the position of the term whose info shall be shown.
         * @return this extension's term information.
         */
        List<String> getTooltipStrings(MainWindow mainWindow, PosInSequent pos);
    }

    /**
     * This interface describes the UI extension to add a components into the status line (right
     * side) of the main window.
     *
     * @author Alexander Weigl
     */
    interface StatusLine {
        /**
         * @return non-null, emptiable list of components
         */
        List<JComponent> getStatusLineComponents();
    }

    /**
     * This interface describes the UI extension to add a {@link SettingsProvider} into the default
     * settings dialog.
     *
     * @author Alexander Weigl
     */
    interface Settings {
        /**
         * @return non-null settings provider
         */
        SettingsProvider getSettings();
    }

    /**
     * Extension Point for defining keyboard shortcuts for various components.
     *
     * @see KeyStrokeManager
     */
    interface KeyboardShortcuts {
        String SEQUENT_VIEW = SequentView.class.getName();
        String GOAL_LIST = GoalList.class.getName();
        String PROOF_TREE_VIEW = ProofTreeView.class.getName();
        String MAIN_WINDOW = MainWindow.class.getName();
        String INFO_VIEW = InfoView.class.getName();
        String STRATEGY_SELECTION_VIEW = StrategySelectionView.class.getName();
        String SOURCE_VIEW = SourceView.class.getName();

        /**
         * @param
         * @param mediator
         * @param component
         * @return non-null settings provider
         */
        Collection<Action> getShortcuts(KeYMediator mediator, String componentId,
                JComponent component);
    }

    /**
     * Extension interface for the term info string in the status line.
     *
     * @author lanzinger
     * @see de.uka.ilkd.key.gui.nodeviews.SequentViewInputListener
     * @see MainWindow#setStatusLine(String)
     */
    interface TermInfo {
        /**
         * @param mainWindow the main window.
         * @param pos the position of the term whose info shall be shown.
         * @return this extension's term information.
         */
        @Nonnull
        List<String> getTermInfoStrings(@Nonnull MainWindow mainWindow, @Nonnull PosInSequent pos);

        default int getTermLabelPriority() {
            return 0;
        }
    }
}
