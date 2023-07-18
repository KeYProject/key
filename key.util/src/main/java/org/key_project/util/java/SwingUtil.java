package org.key_project.util.java;

import javax.swing.*;
import javax.swing.table.TableCellRenderer;
import javax.swing.table.TableColumn;
import java.awt.*;
import java.awt.event.KeyEvent;

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
     * Resize the columns in the provided table to match their content.
     * Will keep 20 pixels of padding between columns.
     *
     * @param table the table
     */
    public static void resizeTableColumns(JTable table) {
        // https://stackoverflow.com/a/31977776/5837178

        for (int column = 0; column < table.getColumnCount(); column++)
        {
            TableColumn tableColumn = table.getColumnModel().getColumn(column);
            int preferredWidth = tableColumn.getMinWidth();
            int maxWidth = tableColumn.getMaxWidth();

            for (int row = 0; row < table.getRowCount(); row++)
            {
                TableCellRenderer cellRenderer = table.getCellRenderer(row, column);
                Component c = table.prepareRenderer(cellRenderer, row, column);
                int width = c.getPreferredSize().width + table.getIntercellSpacing().width + 20;
                preferredWidth = Math.max(preferredWidth, width);

                //  We've exceeded the maximum width, no need to check other rows

                if (preferredWidth >= maxWidth)
                {
                    preferredWidth = maxWidth;
                    break;
                }
            }

            tableColumn.setPreferredWidth( preferredWidth );
        }
    }

    /**
     * Register an event listener that will close the dialog when the user presses
     * the escape key.
     *
     * @param dialog the dialog
     */
    public static void closeDialogOnEscape(JDialog dialog) {
        KeyStroke stroke = KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0);
        dialog.getRootPane().registerKeyboardAction(e -> dialog.dispose(), stroke, JComponent.WHEN_IN_FOCUSED_WINDOW);
    }
}
