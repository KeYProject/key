package de.uka.ilkd.key.gui.extension.api;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsProvider;

import javax.swing.*;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
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
        String name() default "";

        boolean optional() default false;

        boolean disabled() default false;

        int priority() default 0;
    }

    interface MainMenu {
        /**
         * @param mainWindow
         * @return
         */
        List<Action> getMainMenuActions(MainWindow mainWindow);


        /**
         * @return
         */
        default int getPriority() {
            return 0;
        }
    }

    /**
     * This interface describes the UI extension point
     * on the left bottom corner (JTabbedPane).
     * <p>
     * You can add various panels to the UI by implementing this
     * interface and announcing it via the {@link java.util.ServiceLoader}.
     * <p>
     * Before mounting on the UI, the {@link LeftPanel#init(MainWindow, KeYMediator)}
     * is called for injecting the dependencies.
     *
     * @author Alexander Weigl
     * @version 1 (07.02.19)
     */
    interface LeftPanel {
        /**
         * @param window
         * @param mediator
         */
        public void init(MainWindow window, KeYMediator mediator);

        /**
         * The title of the tab pane for the user.
         *
         * @return non-null and non-empty string
         */
        public String getTitle();

        /**
         * A nice icon for viewing aside to the tab title.
         *
         * @return
         */
        public default Icon getIcon() {
            return null;
        }

        /**
         * The content of the tab pane
         *
         * @return
         */
        public JComponent getComponent();


        /**
         * @return
         */
        public default int priority() {
            return 0;
        }
    }

    interface ContextMenu {
        /**
         * @param mainWindow non-null
         * @return a list of actions
         */
        List<Action> getContextActions(MainWindow mainWindow, ContextMenuKind kind, Object underlyingObject);
    }

    interface Toolbar {
        JToolBar getToolbar(MainWindow mainWindow);
    }

    interface StatusLine {
        List<JComponent> getStatusLineComponents();
    }

    public interface Settings {
        SettingsProvider getSettings();
    }
}
