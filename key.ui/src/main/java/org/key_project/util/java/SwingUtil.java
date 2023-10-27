/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.java;


import java.awt.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import javax.swing.*;

import bibliothek.gui.dock.themes.basic.BasicDockableDisplayer;

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
     * This will search the view hierarchy recursively.
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
     * Find all components of the specified class in the container.
     * This will search the view hierarchy recursively and is limited
     * to "visible" elements (on screen or on visible tab).
     *
     * @param container container to search in
     * @param classToFind class to look for
     * @return the object(s) if found (may be empty)
     * @param <T> class of the component
     */
    public static <T> List<T> findAllComponents(Container container, Class<T> classToFind) {
        List<T> l = new ArrayList<>();
        for (int i = 0; i < container.getComponentCount(); i++) {
            var c = container.getComponent(i);
            // if the docking container is visible, we consider all tabs in the search
            if (!c.isVisible() && !(c instanceof BasicDockableDisplayer)) {
                continue;
            }

            if (classToFind.isAssignableFrom(c.getClass())) {
                l.add((T) c);
            } else if (c instanceof Container) {
                var f = findAllComponents((Container) c, classToFind);
                l.addAll(f);
            }
            if (c instanceof JMenu) {
                var queue = new HashSet<JMenu>();
                queue.add((JMenu) c);
                while (!queue.isEmpty()) {
                    var newQ = new HashSet<JMenu>();
                    for (var menu : queue) {
                        for (int j = 0; j < menu.getItemCount(); j++) {
                            var item = menu.getItem(j);
                            if (item == null) {
                                continue;
                            }
                            if (item instanceof JMenu) {
                                newQ.add((JMenu) item);
                            }
                            if (classToFind.isAssignableFrom(item.getClass())) {
                                l.add((T) item);
                            }
                        }
                    }
                    queue = newQ;
                }
            }
        }
        return l;
    }

    public static Collection<Window> getAllOpenWindows() {
        var l = new HashSet<Window>();

        Set<Window> q = new HashSet<>();
        q.addAll(Arrays.asList(Window.getWindows()));
        q.addAll(Arrays.asList(Window.getOwnerlessWindows()));
        while (!q.isEmpty()) {
            var newQ = new HashSet<Window>();

            for (var window : q) {
                if (l.contains(window)) {
                    continue;
                }
                l.add(window);
                newQ.addAll(Arrays.asList(window.getOwnedWindows()));
            }
            q = newQ;
        }

        return l;
    }

    public static List<JPopupMenu> getPopups() {
        MenuSelectionManager msm = MenuSelectionManager.defaultManager();
        MenuElement[] p = msm.getSelectedPath();

        List<JPopupMenu> list = new ArrayList<>();
        for (MenuElement element : p) {
            if (element instanceof JPopupMenu) {
                list.add((JPopupMenu) element);
            }
        }
        return list;
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

    /**
     * Set the provided font on the component and recursively on all children components.
     *
     * @param component the component
     * @param font the font
     */
    public static void setFont(JComponent component, Font font) {
        if (component == null) {
            return;
        }
        component.setFont(font);
        for (int i = 0; i < component.getComponentCount(); i++) {
            Component c = component.getComponent(i);
            if (c == null) {
                continue;
            }
            c.setFont(font);
            if (c instanceof JComponent) {
                setFont((JComponent) c, font);
            }
        }
        // JMenu hides its entries in the popup menu
        if (component instanceof JMenu && ((JMenu) component).getPopupMenu() != null) {
            setFont(((JMenu) component).getPopupMenu(), font);
        }
    }
}
