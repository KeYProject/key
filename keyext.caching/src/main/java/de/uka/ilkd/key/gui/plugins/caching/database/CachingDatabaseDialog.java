/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching.database;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import java.io.IOException;
import javax.swing.*;

import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;

import org.key_project.util.java.SwingUtil;

import net.miginfocom.layout.AC;
import net.miginfocom.layout.LC;
import net.miginfocom.swing.MigLayout;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class CachingDatabaseDialog extends JDialog {
    private static final Logger LOGGER = LoggerFactory.getLogger(CachingDatabaseDialog.class);

    private CachingDatabase database;
    private JTable databaseTable;

    public CachingDatabaseDialog(CachingDatabase database) {
        super(MainWindow.getInstance(), "Proof Caching Database");

        this.database = database;

        var contentPane = new JPanel();
        contentPane
                .setLayout(new MigLayout(new LC().fillX().wrapAfter(1), new AC().align("left", 0)));
        setContentPane(contentPane);

        var statusPane = new JLabel("Database status: OK");
        contentPane.add(statusPane);

        var buttonPane = new JPanel();
        var deleteAllButton = new JButton("Reset database");
        deleteAllButton.addActionListener(e -> resetDatabase());
        buttonPane.add(deleteAllButton);
        contentPane.add(buttonPane);

        var tableModel = new CachingDatabaseTable(database);
        databaseTable = new JTable(tableModel);
        databaseTable.setAutoResizeMode(JTable.AUTO_RESIZE_OFF);
        SwingUtil.resizeTableColumns(databaseTable);
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

    public static KeyAction getOpenAction(CachingDatabase database) {
        return new CachingDatabaseOpenAction(database);
    }

    private static final class CachingDatabaseOpenAction extends KeyAction {
        private CachingDatabase database;

        CachingDatabaseOpenAction(CachingDatabase database) {
            this.database = database;
            setName("Open proof caching database");
            setMenuPath("Proof.Proof Caching");
            setAcceleratorLetter(KeyEvent.VK_D);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            new CachingDatabaseDialog(database);
        }
    }
}
