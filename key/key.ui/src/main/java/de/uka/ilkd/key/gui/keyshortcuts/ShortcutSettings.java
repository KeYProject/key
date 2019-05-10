package de.uka.ilkd.key.gui.keyshortcuts;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.settings.InvalidSettingsInputException;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsProvider;

import javax.swing.*;
import javax.swing.table.AbstractTableModel;
import java.awt.*;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.util.Collections;
import java.util.List;
import java.util.Properties;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (09.05.19)
 */
public class ShortcutSettings extends JPanel implements SettingsProvider {
    private final JTable tblShortcuts = new JTable();
    private ShortcutsTableModel modelShortcuts;

    public ShortcutSettings() {
        setLayout(new BorderLayout());
        JComponent pNorth = SettingsManager.createSettingsHeaderPanel(
                "Keyboard Shortcuts", "");

        tblShortcuts.setModel(new ShortcutsTableModel(Collections.emptyList(),
                Collections.emptyList(), Collections.emptyList()));

        add(pNorth, BorderLayout.NORTH);
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

        List<String> actionNames = p.keySet().stream().sorted().map(Object::toString).collect(Collectors.toList());
        List<String> shortcuts = actionNames.stream().map(p::getProperty).collect(Collectors.toList());
        List<Action> actions = actionNames.stream()
                .map(KeyStrokeManager::findAction)
                .collect(Collectors.toList());

        modelShortcuts = new ShortcutsTableModel(actionNames, shortcuts, actions);
        tblShortcuts.setModel(modelShortcuts);

        JTextField txtCaptureShortcut = new JTextField();
        DefaultCellEditor cellEditor = new DefaultCellEditor(txtCaptureShortcut);
        txtCaptureShortcut.addKeyListener(new KeyAdapter() {
            @Override
            public void keyTyped(KeyEvent e) {
                //KeyStroke ks = KeyStroke.getKeyStrokeForEvent(e);
                //txtCaptureShortcut.setText(ks.toString());
            }

            @Override
            public void keyPressed(KeyEvent e) {
                if (e.getKeyCode() == KeyEvent.VK_UNDEFINED) {
                    e.consume();
                    return;
                }

                KeyStroke ks = KeyStroke.getKeyStrokeForEvent(e);
                txtCaptureShortcut.setText(ks.toString());

                //System.out.println(ks);
                boolean shortcutComplete =
                        ks.getModifiers() > 0
                                && ks.getKeyCode() != KeyEvent.VK_UNDEFINED
                                && ks.getKeyCode() != KeyEvent.VK_CONTROL
                                && ks.getKeyCode() != KeyEvent.VK_ALT;

                if (shortcutComplete)
                    cellEditor.stopCellEditing();
            }

            @Override
            public void keyReleased(KeyEvent e) {
                //KeyStroke ks = KeyStroke.getKeyStrokeForEvent(e);
                //txtCaptureShortcut.setText(ks.toString());
            }
        });
        tblShortcuts.getColumnModel()
                .getColumn(2).setCellEditor(cellEditor);

        return this;
    }

    @Override
    public void applySettings(MainWindow window)
            throws InvalidSettingsInputException {

        List<String> s = modelShortcuts.shortcut.stream()
                .filter(it -> it == null || it.isEmpty())
                .collect(Collectors.toList());

        for (int i = 0; i < s.size() - 1; i++) {
            for (int j = i + 1; j < s.size(); j++) {
                if (s.get(i).equals(s.get(j))) {
                    //found duplicate
                    throw new InvalidSettingsInputException(
                            String.format("<html>Clash of key bindings: %s<br>For keys: %s and %s",
                                    s.get(i),
                                    modelShortcuts.actionName.get(i),
                                    modelShortcuts.actionName.get(j)),
                            this, tblShortcuts);
                }
            }
        }

        List<KeyStroke> keystrokes = modelShortcuts.shortcut
                .stream().map(KeyStroke::getKeyStroke)
                .collect(Collectors.toList());

        if (keystrokes.contains(null)) {
            throw new InvalidSettingsInputException(
                    "<html>Invalid keystroke specified",
                    this, tblShortcuts);
        }

        for (int i = 0; i <= modelShortcuts.shortcut.size(); i++) {
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
        private static final String[] COLUMNS = new String[]{"Name", "Description", "Shortcut"};
        private final List<String> actionName;
        private final List<String> shortcut;
        private final List<Action> actions;

        private ShortcutsTableModel(List<String> actionName, List<String> shortcut, List<Action> actions) {
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
                    return actionName.get(rowIndex);
                case 1:
                    Action a = actions.get(rowIndex);
                    if (a == null) return "";
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
