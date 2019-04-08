package de.uka.ilkd.key.gui.settings;

import com.sun.tools.javac.Main;
import de.uka.ilkd.key.gui.MainWindow;

import javax.swing.*;
import javax.swing.tree.TreeNode;
import java.util.Collections;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 */
public interface SettingsProvider {
    /**
     *
     * @return
     */
    String getDescription();

    /**
     *
     * @param window
     * @return
     */
    JComponent getPanel(MainWindow window);

    /**
     *
     * @return
     */
    default List<SettingsProvider> getChildren() {
        return Collections.emptyList();
    }

    /**
     *
     */
    void applySettings(MainWindow window);

    /**
     *
     * @return
     */
    default Icon getIcon() {
        return null;
    }

    /**
     *
     * @param substring
     * @return
     */
    default boolean contains(String substring) {
        return false;
    }

    /**
     *
     * @return
     */
    default int getPriorityOfSettings() {
        return 0;
    }
}
