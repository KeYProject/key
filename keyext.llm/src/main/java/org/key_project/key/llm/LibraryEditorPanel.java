/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.FlowLayout;
import java.util.ArrayList;
import java.util.List;
import javax.swing.*;
import javax.swing.table.DefaultTableModel;

import org.jspecify.annotations.Nullable;

/**
 * Embedded editor for a file-backed user library (prompts or skills) that is shown as its own
 * settings-tree node below "LLM Settings" (see {@code LlmExtension.LlmSettingsProvider}: a table
 * lists the entries, the form below edits a selection and {@code New}/{@code Save}/{@code Delete}
 * manage the library. Persistence is immediate (the library is written on {@code Save}), it is
 * not deferred to the settings {@code Apply} button.
 *
 * @param <E> the library element type
 * @author Alexander Weigl
 */
public abstract class LibraryEditorPanel<E> extends JPanel {
    private static final String[] COLUMNS = { "Name", "Description" };

    private final List<E> items = new ArrayList<>();
    private final JTable table = new JTable();
    private final DefaultTableModel tableModel = new DefaultTableModel(COLUMNS, 0) {
        @Override
        public boolean isCellEditable(int row, int column) {
            return false;
        }
    };
    private final JLabel status = new JLabel(" ");
    private final JPanel formArea = new JPanel(new BorderLayout());
    private @Nullable String editingName;

    protected final JTextField txtName = new JTextField(20);
    protected final JTextField txtDescription = new JTextField(20);

    protected LibraryEditorPanel() {
        super(new BorderLayout(8, 8));
        table.setModel(tableModel);
        table.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        table.getSelectionModel().addListSelectionListener(e -> {
            if (e.getValueIsAdjusting()) {
                return;
            }
            int row = table.getSelectedRow();
            if (row >= 0 && row < items.size()) {
                editingName = nameOf(items.get(row));
                populateForm(items.get(row));
                status.setText(" ");
            }
        });

        var actions = new JPanel(new FlowLayout(FlowLayout.LEFT, 4, 0));
        actions.add(button("New", this::startNew));
        actions.add(button("Save", this::saveForm));
        actions.add(button("Delete", this::deleteCurrent));

        var center = new JPanel(new BorderLayout(4, 4));
        center.add(new JScrollPane(table), BorderLayout.CENTER);
        center.add(actions, BorderLayout.SOUTH);
        add(center, BorderLayout.CENTER);

        status.setForeground(Color.RED);
        formArea.add(status, BorderLayout.SOUTH);
        add(formArea, BorderLayout.SOUTH);
    }

    private static JButton button(String text, Runnable action) {
        var b = new JButton(text);
        b.addActionListener(e -> action.run());
        return b;
    }

    // ------------------------------------------------------------------ for subclasses

    /** Places the form (built with the subclass fields) above the status label. */
    protected final void setForm(JComponent form) {
        formArea.add(form, BorderLayout.CENTER);
    }

    /** Reloads the table from the library and resets the editor. */
    protected final void reload() {
        editingName = null;
        table.clearSelection();
        tableModel.setRowCount(0);
        items.clear();
        items.addAll(loadAll());
        for (var e : items) {
            tableModel.addRow(new Object[] { nameOf(e), descriptionOf(e) });
        }
        populateForm(null);
        status.setText(" ");
    }

    /** Selects the row with the given name and loads it into the form. */
    protected final void selectByName(String name) {
        for (int i = 0; i < items.size(); i++) {
            if (nameOf(items.get(i)).equals(name)) {
                table.setRowSelectionInterval(i, i);
                return;
            }
        }
    }

    /** Number of rows currently shown (used by tests). */
    final int tableRowCount() {
        return table.getRowCount();
    }

    // ------------------------------------------------------------- library hooks (subclass)

    /** All entries of the library. */
    protected abstract List<E> loadAll();

    protected abstract String nameOf(E e);

    protected abstract String descriptionOf(E e);

    /** Fills the form from {@code e}, or clears it when {@code e} is {@code null}. */
    protected abstract void populateForm(@Nullable E e);

    /** Builds an element from the current form values. */
    protected abstract E formData();

    /** Persists the element; returns {@code null} on success or an error message. */
    protected abstract String store(E e);

    /** Deletes the entry with the given name; returns {@code null} on success or an error. */
    protected abstract String removeByName(String name);

    // ----------------------------------------------------------------------- editor actions

    private void startNew() {
        editingName = null;
        table.clearSelection();
        populateForm(null);
        status.setText(" ");
    }

    private void saveForm() {
        var data = formData();
        var newName = nameOf(data);
        if (newName == null || newName.isBlank()) {
            status.setText("Please enter a name.");
            return;
        }
        var error = store(data);
        if (error != null) {
            status.setText(error);
            return;
        }
        // a renamed entry is stored under the new id and the old file is removed
        if (editingName != null && !editingName.equals(newName)) {
            removeByName(editingName);
        }
        reload();
        selectByName(newName);
    }

    private void deleteCurrent() {
        if (editingName == null) {
            status.setText("Select an entry to delete.");
            return;
        }
        var error = removeByName(editingName);
        if (error != null) {
            status.setText(error);
            return;
        }
        reload();
    }
}
