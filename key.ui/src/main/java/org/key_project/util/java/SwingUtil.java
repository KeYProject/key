/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.java;


import java.awt.*;
import java.io.IOException;
import java.net.URI;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import javax.swing.*;

import de.uka.ilkd.key.gui.fonticons.IconFactory;

import bibliothek.gui.dock.themes.basic.BasicDockableDisplayer;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Utilities for working with Swing.
 *
 * @author Arne Keller
 */
public final class SwingUtil {
    public static final Logger LOGGER = LoggerFactory.getLogger(SwingUtil.class);
    private static final String NOTIFICATION_ERROR = "failed to show notification ";


    private SwingUtil() {
    }

    /**
     * Wrapper for {@link java.awt.Desktop#browse(URI)} that also works on Linux.
     *
     * @param uri the URI to be displayed in the user's default browser
     */
    public static void browse(URI uri) throws IOException {
        LOGGER.info("Open {}", uri);
        try {
            Desktop.getDesktop().browse(uri);
        } catch (UnsupportedOperationException e) {
            if (System.getProperty("os.name").startsWith("Linux")) {
                // try fallback: xdg-open
                Runtime.getRuntime().exec(new String[] { "xdg-open", uri.toString() });
            } else {
                throw e;
            }
        }
    }

    /**
     * Wrapper for {@link Desktop#isSupported(Desktop.Action)} BROWSE that always returns true on
     * Linux.
     *
     * @return whether BROWSE is supported
     * @see #browse(URI)
     */
    public static boolean browseIsSupported() {
        return Desktop.getDesktop().isSupported(Desktop.Action.BROWSE)
                || System.getProperty("os.name").startsWith("Linux");
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

    /**
     * Show a desktop notification to the user.
     *
     * @param title title of the notification
     * @param text text of the notification
     */
    public static void showNotification(String title, String text) {
        if (System.getProperty("os.name").startsWith("Linux")) {
            // Linux: try notify-send (looks better than SystemTray)
            try {
                new CheckedProcessBuilder("notify-send", new String[] { "-?" })
                        .start("-a", "KeY", title, text);
            } catch (IOException | InterruptedException e) {
                // since we checked for notify-send previously, this error is unlikely
                LOGGER.warn(NOTIFICATION_ERROR, e);
            }
        } else if (System.getProperty("os.name").startsWith("Mac")) {
            // macOS: show a native notification
            try {
                new CheckedProcessBuilder("osascript", new String[] { "-e", "return \"\"" })
                        .start("-e",
                            "display notification \"%s\" with title \"%s\"".formatted(text, title));
            } catch (IOException | InterruptedException e) {
                // since we checked for osascript previously, this error is unlikely
                LOGGER.warn(NOTIFICATION_ERROR, e);
            }
        } else {
            // else: use the Java API
            // this will show a native notification on Windows 10/11 at least
            SystemTray tray = null;
            TrayIcon trayIcon = null;
            try {
                tray = SystemTray.getSystemTray();
                if (tray == null) {
                    LOGGER.warn(NOTIFICATION_ERROR + "(tray null)");
                    return;
                }

                trayIcon = new TrayIcon(IconFactory.keyLogo(), "KeY");
                // Let the system resize the image if needed
                trayIcon.setImageAutoSize(true);
                tray.add(trayIcon);
                trayIcon.displayMessage(title, text, TrayIcon.MessageType.NONE);
            } catch (AWTException e) {
                LOGGER.warn(NOTIFICATION_ERROR, e);
            } finally {
                if (tray != null && trayIcon != null) {
                    tray.remove(trayIcon);
                }
            }
        }
    }
}
