package de.uka.ilkd.key.gui.extension.api;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsProvider;

import javax.swing.*;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.util.Collection;
import java.util.List;

/**
 * A marker interface for extension of the KeY GUI.
 * Every extension should implement this interface and should be registered in a service loader file
 * <code>META-INF/services/KeYGuiExtension</code>.
 * <p>
 * This interface comes works in combination with the annotation {@see KeYGuiExtension#Info}
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
    }

    /**
     * Main Menu extension provides entry to the extension {@link JMenu} in the main frame.
     */
    interface MainMenu {
        /**
         * A list of actions which should be added to the main menu.
         * <p>
         * Actions should use the {@link KeYExtConstants#PATH} and {@link KeYExtConstants#PRIORITY} to control their
         * position in the menu.
         *
         * @param mainWindow the window of the main menu
         * @return non-null, emptiable list of actions.
         * @see de.uka.ilkd.key.gui.actions.KeyAction
         */
        List<Action> getMainMenuActions(MainWindow mainWindow);
    }

    /**
     * Simplest extension point. Called during after the initialization of the {@link MainWindow}.
     * Can be used for registering key binding.
     */
    interface Startup {
        void init(MainWindow window, KeYMediator mediator);
    }

    /**
     * This interface describes the UI extension point
     * on the left bottom corner (JTabbedPane).
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
         * @param window   parent of this extension
         * @param mediator the current mediator
         */
        Collection<TabPanel> getPanels(MainWindow window, KeYMediator mediator);
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
         * Actions should use the {@link KeYExtConstants#PATH} and {@link KeYExtConstants#PRIORITY} to control their
         * position in the menu.
         *
         * @param mediator       the window of the main menu
         * @param kind             the type of context menu
         * @param underlyingObject the object for which the context menu is requested
         * @return non-null, emptiable list of actions.
         * @see de.uka.ilkd.key.gui.actions.KeyAction
         */
        List<Action> getContextActions(KeYMediator mediator, ContextMenuKind kind, Object underlyingObject);
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
        JToolBar getToolbar(MainWindow mainWindow);
    }

    /**
     * This interface describes the UI extension to add a components
     * into the status line (right side) of the main window.
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
     * This interface describes the UI extension to add a {@link SettingsProvider}
     * into the default settings dialog.
     *
     * @author Alexander Weigl
     */
    interface Settings {
        /**
         * @return non-null settings provider
         */
        SettingsProvider getSettings();
    }
}
