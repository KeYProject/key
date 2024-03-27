/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching.database;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.IOException;
import java.util.Arrays;
import javax.swing.*;

import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;

import org.key_project.util.java.NumberUtil;
import org.key_project.util.java.SwingUtil;

import net.miginfocom.layout.AC;
import net.miginfocom.layout.LC;
import net.miginfocom.swing.MigLayout;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class CachingDatabaseDialog extends JDialog {
    private static final Logger LOGGER = LoggerFactory.getLogger(CachingDatabaseDialog.class);

    /**
     * The database to show in the dialog.
     */
    private final CachingDatabase database;
    /**
     * The table showing the entries in the database.
     */
    private final JTable databaseTable;
    /**
     * Button to delete selected rows in the database.
     */
    private final JButton deletedSelected;
    /**
     * Data model of the {@link #databaseTable}.
     */
    private final CachingDatabaseTable tableModel;

    /**
     * Create a new dialog.
     *
     * @param database the database to show
     */
    public CachingDatabaseDialog(CachingDatabase database) {
        super(MainWindow.getInstance(), "Proof Caching Database");

        this.database = database;

        var contentPane = new JPanel();
        contentPane
                .setLayout(new MigLayout(new LC().fillX().wrapAfter(1), new AC().align("left", 0)));
        setContentPane(contentPane);

        var statusPane = new JLabel("Database status: OK");
        contentPane.add(statusPane);

        try {
            var metadataSizePane = new JLabel(String.format("Size of database metadata: %s",
                NumberUtil.formatAsHumanReadableSize(database.sizeOfMetadata())));
            contentPane.add(metadataSizePane);

            var totalSizePane = new JLabel(String.format("Size of database: %s",
                NumberUtil.formatAsHumanReadableSize(database.sizeOfCacheFiles())));
            contentPane.add(totalSizePane);
        } catch (IOException e) {
            // this is hardly critical functionality, so don't bother creating fallback labels
            LOGGER.warn("failed to determine database size ", e);
        }

        var buttonPane = new JPanel();
        var deleteAllButton = new JButton("Reset database");
        deleteAllButton.addActionListener(e -> resetDatabase());
        buttonPane.add(deleteAllButton);
        contentPane.add(buttonPane);

        deletedSelected = new JButton("Deleted selected proof(s)");
        deletedSelected.addActionListener(e -> deletedSelected());
        contentPane.add(deletedSelected);

        tableModel = new CachingDatabaseTable(database);
        databaseTable = new JTable(tableModel);
        databaseTable.setAutoResizeMode(JTable.AUTO_RESIZE_OFF);
        SwingUtil.resizeTableColumns(databaseTable);

        // popup menu for table entries
        var tablePopupMenu = new JPopupMenu();
        var deleteMenuItem = new JMenuItem("Delete");
        deleteMenuItem.addActionListener(e -> deletedSelected());
        tablePopupMenu.add(deleteMenuItem);
        databaseTable.setComponentPopupMenu(tablePopupMenu);
        databaseTable.addMouseListener(new OpenPopupMenu(tablePopupMenu));

        var scrollPane =
            new JScrollPane(databaseTable, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
                ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
        Dimension dim = new Dimension(databaseTable.getPreferredSize());
        int scrollbarWidth = (Integer) UIManager.get("ScrollBar.width");
        dim.width += scrollbarWidth + 2;
        dim.height =
            Math.min(scrollPane.getPreferredSize().height, dim.height + scrollbarWidth + 30);
        scrollPane.setPreferredSize(dim);
        contentPane.add(scrollPane, "grow");

        SwingUtil.closeDialogOnEscape(this);

        pack();
        setMinimumSize(new Dimension(800, 600));
        setLocationRelativeTo(MainWindow.getInstance());
        setVisible(true);
    }

    private void refreshUI() {
        ((CachingDatabaseTable) databaseTable.getModel()).refresh();
        ((CachingDatabaseTable) databaseTable.getModel()).fireTableDataChanged();
        databaseTable.invalidate();
        invalidate();
    }

    private void resetDatabase() {
        try {
            database.reset();
            refreshUI();
        } catch (IOException e) {
            LOGGER.error("failed to reset database ", e);
            IssueDialog.showExceptionDialog(this, e);
        }
    }

    private void deletedSelected() {
        int[] toDelete = databaseTable.getSelectedRows();
        Arrays.sort(toDelete);
        for (int i = toDelete.length - 1; i >= 0; i--) {
            try {
                tableModel.deleteProof(toDelete[i]);
            } catch (IOException ex) {
                LOGGER.warn("failed to delete proof ", ex);
                IssueDialog.showExceptionDialog(this, ex);
            }
        }
        refreshUI();
    }

    public static KeyAction getOpenAction(CachingDatabase database) {
        return new CachingDatabaseOpenAction(database);
    }

    private static final class CachingDatabaseOpenAction extends KeyAction {
        private CachingDatabase database;

        CachingDatabaseOpenAction(CachingDatabase database) {
            this.database = database;
            setName("Show Proof Caching Database");
            setMenuPath("Options");
            setAcceleratorLetter(KeyEvent.VK_D);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            new CachingDatabaseDialog(database);
        }
    }

    private static class OpenPopupMenu extends MouseAdapter {
        /**
         * The popup menu to show if the relevant mouse button is pressed.
         */
        private final JPopupMenu tablePopupMenu;

        public OpenPopupMenu(JPopupMenu tablePopupMenu) {
            this.tablePopupMenu = tablePopupMenu;
        }

        @Override
        public void mousePressed(MouseEvent e) {
            if (e.isPopupTrigger()) {
                JTable source = (JTable) e.getSource();
                int row = source.rowAtPoint(e.getPoint());
                int column = source.columnAtPoint(e.getPoint());

                if (!source.isRowSelected(row)) {
                    source.changeSelection(row, column, false, false);
                }

                tablePopupMenu.show(e.getComponent(), e.getX(), e.getY());
            }
        }
    }
}
