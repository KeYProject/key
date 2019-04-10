package de.uka.ilkd.key.gui.settings;

import de.uka.ilkd.key.gui.MainWindow;

import javax.swing.*;
import java.util.Collections;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
public interface SettingsProvider {
    /**
     * A textual human readable description of the settings panel.
     * Used at the overview tree at the left.
     *
     * @return non-null non-empty string
     */
    String getDescription();

    /**
     * @param window
     * @return
     */
    JComponent getPanel(MainWindow window);

    /**
     * @return
     */
    default List<SettingsProvider> getChildren() {
        return Collections.emptyList();
    }

    /**
     *
     */
    void applySettings(MainWindow window) throws Exception;

    /**
     * @return
     * @deprecated unused currently
     */
    @Deprecated
    default Icon getIcon() {
        return null;
    }

    /**
     * @param substring
     * @return
     */
    default boolean contains(String substring) {
        return false;
    }

    /**
     * @return
     */
    default int getPriorityOfSettings() {
        return 0;
    }
}
