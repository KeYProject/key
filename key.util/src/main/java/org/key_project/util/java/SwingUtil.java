package org.key_project.util.java;

import java.awt.*;
import javax.swing.*;

/**
 * Utilities for working with Swing.
 *
 * @author Arne Keller
 */
public final class SwingUtil {
    private SwingUtil() {
    }

    /**
     * Find a component of the specified class in the container.
     * This will search recursively.
     *
     * @param container container to search in
     * @param classToFind class to look for
     * @return the object if found, otherwise null
     * @param <T> class of the component
     */
    public static <T> T findComponent(Container container, Class<T> classToFind) {
        for (int i = 0; i < container.getComponentCount(); i++) {
            var c = container.getComponent(i);
            if (c.getClass().equals(classToFind)) {
                return (T) c;
            } else if (c instanceof Container) {
                var f = findComponent((Container) c, classToFind);
                if (f != null) {
                    return f;
                }
            }
        }
        return null;
    }

    /**
     * Create a scroll pane around the given table.
     * It will always have vertical and horizontal scroll bars.
     *
     * @param table the table
     * @return the scroll pane
     */
    public static JScrollPane createScrollPane(JTable table) {
        var scrollPane = new JScrollPane(table, ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS,
            ScrollPaneConstants.HORIZONTAL_SCROLLBAR_ALWAYS);

        Dimension dim = new Dimension(table.getPreferredSize());
        dim.width += (Integer) UIManager.get("ScrollBar.width") + 2;
        dim.height = scrollPane.getPreferredSize().height;
        scrollPane.setPreferredSize(dim);

        return scrollPane;
    }
}
