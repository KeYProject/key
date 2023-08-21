/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.keyshortcuts;

import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;
import java.util.stream.Collectors;
import javax.swing.*;
import javax.swing.table.AbstractTableModel;
import javax.swing.table.TableRowSorter;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.gui.settings.SimpleSettingsPanel;

/**
 * UI for configuring the {@link KeyStroke}s inside KeY.
 *
 * @author Alexander Weigl
 * @version 1 (09.05.19)
 */
public class ShortcutSettings extends SimpleSettingsPanel implements SettingsProvider {
    private static final long serialVersionUID = -7609149706562761596L;
    private final JTable tblShortcuts = new JTable();
    private ShortcutsTableModel modelShortcuts;

    public ShortcutSettings() {
        super();
        setHeaderText("Keyboard Shortcuts");
        setSubHeaderText(
            "These settings are stored in " + KeyStrokeSettings.SETTINGS_FILE.getAbsolutePath());
        add(new JScrollPane(tblShortcuts));
    }

    @Override
    public String getDescription() {
        return "Keyboard Shortcuts";
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        KeyStrokeSettings settings = KeyStrokeManager.getSettings();
        Properties p = new Properties();
        settings.writeSettings(p);

        List<String> actionNames =
            p.keySet().stream().sorted().map(Object::toString).collect(Collectors.toList());

        // for the view, we hide "pressed" to increase readability
        List<String> shortcuts = actionNames.stream().map(p::getProperty)
                .map(s -> s.replace("pressed ", "")).collect(Collectors.toList());

        List<Action> actions =
            actionNames.stream().map(KeyStrokeManager::findAction).collect(Collectors.toList());

        modelShortcuts = new ShortcutsTableModel(actionNames, shortcuts, actions);
        tblShortcuts.setModel(modelShortcuts);

        TableRowSorter<ShortcutsTableModel> sorter = new TableRowSorter<>(modelShortcuts);
        tblShortcuts.setRowSorter(sorter);

        List<RowSorter.SortKey> sortKeys = new ArrayList<>(25);
        sortKeys.add(new RowSorter.SortKey(0, SortOrder.ASCENDING));
        sorter.setSortKeys(sortKeys);


        JTextField txtCaptureShortcut = new JTextField();
        DefaultCellEditor cellEditor = new DefaultCellEditor(txtCaptureShortcut);
        txtCaptureShortcut.addKeyListener(new KeyAdapter() {
            @Override
            public void keyTyped(KeyEvent e) {
                // KeyStroke ks = KeyStroke.getKeyStrokeForEvent(e);
                // txtCaptureShortcut.setText(ks.toString());
            }

            @Override
            public void keyPressed(KeyEvent e) {
                if (e.getKeyCode() == KeyEvent.VK_UNDEFINED) {
                    e.consume();
                    return;
                }

                KeyStroke ks = KeyStroke.getKeyStrokeForEvent(e);
                // for the view, we hide "pressed" to increase readability
                String shortened = ks.toString().replace("pressed ", "");
                txtCaptureShortcut.setText(shortened);

                boolean shortcutComplete =
                    ks.getModifiers() > 0 && ks.getKeyCode() != KeyEvent.VK_UNDEFINED
                            && ks.getKeyCode() != KeyEvent.VK_CONTROL
                            && ks.getKeyCode() != KeyEvent.VK_SHIFT
                            && ks.getKeyCode() != KeyEvent.VK_ALT;

                if (shortcutComplete) {
                    cellEditor.stopCellEditing();
                }
            }

            @Override
            public void keyReleased(KeyEvent e) {
                // KeyStroke ks = KeyStroke.getKeyStrokeForEvent(e);
                // txtCaptureShortcut.setText(ks.toString());
            }
        });
        tblShortcuts.getColumnModel().getColumn(2).setCellEditor(cellEditor);

        return this;
    }

    @Override
    public void applySettings(MainWindow window) {
        List<String> s = modelShortcuts.shortcut;

        /*
         * weigl: disable duplicate check, because we have many in the default config for (int i =
         * 0; i < s.size() - 1; i++) { for (int j = i + 1; j < s.size(); j++) { String a = s.get(i);
         * String b = s.get(j);
         *
         * if (a == null || b == null || a.isEmpty() || b.isEmpty()) continue;
         *
         * if (a.equals(b)) { //found duplicate throw new InvalidSettingsInputException(
         * String.format("Clash of key bindings: %s<br>For keys: %s and %s", s.get(i),
         * modelShortcuts.actionName.get(i), modelShortcuts.actionName.get(j)), this, tblShortcuts);
         * } } }
         */

        List<KeyStroke> keystrokes =
            s.stream().map(KeyStroke::getKeyStroke).collect(Collectors.toList());
        /*
         * if (keystrokes.contains(null)) { throw new InvalidSettingsInputException(
         * "Invalid keystroke specified", this, tblShortcuts); }
         */

        for (int i = 0; i < modelShortcuts.shortcut.size(); i++) {
            String key = modelShortcuts.actionName.get(i);
            KeyStroke ks = keystrokes.get(i);
            KeyStrokeManager.getSettings().setKeyStroke(key, ks, true);
            Action action = modelShortcuts.actions.get(i);
            if (action != null) {
                action.putValue(Action.ACCELERATOR_KEY, ks);
            }
        }
    }

    private static class ShortcutsTableModel extends AbstractTableModel {
        private static final long serialVersionUID = -2854179933936417703L;
        private static final String[] COLUMNS = new String[] { "Name", "Description", "Shortcut" };
        private final List<String> actionName;
        private final List<String> shortcut;
        private final List<Action> actions;

        private ShortcutsTableModel(List<String> actionName, List<String> shortcut,
                List<Action> actions) {
            this.actionName = actionName;
            this.shortcut = shortcut;
            this.actions = actions;
        }

        @Override
        public int getRowCount() {
            return actionName.size();
        }

        @Override
        public int getColumnCount() {
            return COLUMNS.length;
        }

        @Override
        public String getColumnName(int column) {
            return COLUMNS[column];
        }

        @Override
        public Object getValueAt(int rowIndex, int columnIndex) {
            switch (columnIndex) {
            case 0:
                return actionName.get(rowIndex)
                        // remove common package prefixes
                        .replaceAll("([a-z]\\w*\\.)*", "");
            case 1:
                Action a = actions.get(rowIndex);
                if (a == null) {
                    return "";
                }
                Object val = a.getValue(Action.SHORT_DESCRIPTION);
                return val != null ? val.toString() : "";
            case 2:
                return shortcut.get(rowIndex);
            }
            return "";
        }

        @Override
        public void setValueAt(Object aValue, int rowIndex, int columnIndex) {
            if (columnIndex == 2) {
                shortcut.set(rowIndex, aValue.toString());
            } else {
                super.setValueAt(aValue, rowIndex, columnIndex);
            }
        }

        @Override
        public boolean isCellEditable(int rowIndex, int columnIndex) {
            return columnIndex == 2;
        }
    }
}
