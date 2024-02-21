/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;

import org.key_project.util.java.SwingUtil;

import net.miginfocom.layout.AC;
import net.miginfocom.layout.LC;
import net.miginfocom.swing.MigLayout;

public class CachingDatabaseDialog extends JDialog {
    public CachingDatabaseDialog() {
        super(MainWindow.getInstance(), "Proof Caching Database");

        var contentPane = new JPanel();
        contentPane
                .setLayout(new MigLayout(new LC().fillX().wrapAfter(1), new AC().align("left", 0)));
        setContentPane(contentPane);

        var statusPane = new JLabel();
        if (CachingDatabase.isInUnsafeState()) {
            statusPane.setText("Database status: invalid state");
        } else {
            statusPane.setText("Database status: OK");
        }
        contentPane.add(statusPane);

        var buttonPane = new JPanel();
        var deleteAllButton = new JButton("Reset database");
        var configure = new JButton("Configure auto delete...");
        buttonPane.add(deleteAllButton);
        buttonPane.add(configure);
        contentPane.add(buttonPane);

        CachingDatabase.save();

        var tableModel = new CachingDatabaseTable();
        var table = new JTable(tableModel);
        table.setAutoResizeMode(JTable.AUTO_RESIZE_OFF);
        SwingUtil.resizeTableColumns(table);
        var scrollPane = new JScrollPane(table, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
            ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
        Dimension dim = new Dimension(table.getPreferredSize());
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

    private void resetDatabase() {

    }

    private void configureAutoDelete() {

    }

    public static KeyAction getOpenAction() {
        return new CachingDatabaseOpenAction();
    }

    private static final class CachingDatabaseOpenAction extends KeyAction {
        CachingDatabaseOpenAction() {
            setName("Open proof caching database");
            setMenuPath("Proof.Proof Caching");
            setAcceleratorLetter(KeyEvent.VK_D);
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            new CachingDatabaseDialog();
        }
    }
}
