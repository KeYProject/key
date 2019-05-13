package de.uka.ilkd.key.gui.ext;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;

import javax.swing.*;

/**
 * This interface describes the UI extension point
 * on the left bottom corner (JTabbedPane).
 * <p>
 * You can add various panels to the UI by implementing this
 * interface and announcing it via the {@link java.util.ServiceLoader}.
 *
 * Before mounting on the UI, the {@link KeYPaneExtension#init(MainWindow, KeYMediator)}
 * is called for injecting the dependencies.
 *
 * @author Alexander Weigl
 * @version 1 (07.02.19)
 */
public interface KeYPaneExtension {
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
     * @return
     */
    public default Icon getIcon() {return null;}

    /**
     * The content of the tab pane
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
