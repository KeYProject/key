/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Dialog;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;
import javax.swing.*;
import javax.swing.filechooser.FileNameExtensionFilter;

import de.uka.ilkd.key.gui.settings.SimpleSettingsPanel;

import org.jspecify.annotations.Nullable;

/**
 * Editor for a file-backed user library (prompts or skills) shown as its own settings-tree node
 * below "LLM Settings" (see {@code LlmExtension.LlmSettingsProvider}). The entries are listed in a
 * simple vertical list (name in bold, description below); entries are selectable, created and
 * edited in a modal dialog opened by {@code New} or {@code Edit} (or a double click), deleted with
 * {@code Delete} and the whole library can be exported to or imported from a JSON file.
 *
 * <p>
 * Like every KeY settings panel it renders the standard header (title + optional subtitle) via
 * {@link SimpleSettingsPanel}.
 *
 * @param <E> the library element type
 * @author Alexander Weigl
 */
public abstract class LibraryEditorPanel<E> extends SimpleSettingsPanel {
    private final String title;
    private final List<E> items = new ArrayList<>();
    private final List<EntryRow> rows = new ArrayList<>();
    private final JPanel listBox = new JPanel();
    private final JButton btnEdit = new JButton("Edit");
    private final JButton btnDelete = new JButton("Delete");
    private int selectedIndex = -1;
    private @Nullable JComponent form;

    protected final JTextField txtName = new JTextField(20);
    protected final JTextField txtDescription = new JTextField(20);

    protected LibraryEditorPanel(String description, String subHeader) {
        title = description;
        setHeaderText(description);
        if (subHeader != null && !subHeader.isEmpty()) {
            setSubHeaderText(subHeader);
        }
        pCenter.setLayout(new BorderLayout(8, 8));

        listBox.setLayout(new BoxLayout(listBox, BoxLayout.Y_AXIS));
        listBox.setOpaque(true);

        var actions = new JPanel(new FlowLayout(FlowLayout.LEFT, 4, 0));
        actions.add(button("New", this::newEntry));
        actions.add(btnEdit);
        actions.add(btnDelete);
        actions.add(button("Export...", this::exportLibrary));
        actions.add(button("Import...", this::importLibrary));

        pCenter.add(listBox, BorderLayout.CENTER);
        pCenter.add(actions, BorderLayout.SOUTH);
        updateButtonState();
    }

    private static JButton button(String text, Runnable action) {
        var b = new JButton(text);
        b.addActionListener(e -> action.run());
        return b;
    }

    private void updateButtonState() {
        boolean hasSelection = selectedIndex >= 0 && selectedIndex < items.size();
        btnEdit.setEnabled(hasSelection);
        btnDelete.setEnabled(hasSelection);
    }

    // ------------------------------------------------------------------ for subclasses

    /** Stores the edit form built by the subclass; it is shown in the modal editor dialog. */
    protected final void setFormComponent(JComponent form) {
        this.form = form;
    }

    /** Reloads the list from the library and clears the selection. */
    protected final void reload() {
        items.clear();
        items.addAll(loadAll());
        listBox.removeAll();
        rows.clear();
        if (items.isEmpty()) {
            var hint =
                new JLabel("No " + title.toLowerCase() + " yet - click \"New\" to create one.");
            hint.setForeground(UIManager.getColor("Label.disabledForeground"));
            hint.setBorder(BorderFactory.createEmptyBorder(8, 10, 8, 10));
            listBox.add(hint);
        } else {
            for (int i = 0; i < items.size(); i++) {
                rows.add(new EntryRow(items.get(i), i));
            }
            for (var row : rows) {
                listBox.add(row);
            }
        }
        selectedIndex = -1;
        listBox.revalidate();
        listBox.repaint();
        updateButtonState();
    }

    /** Selects the entry with the given name. */
    protected final void selectByName(String name) {
        for (int i = 0; i < items.size(); i++) {
            if (nameOf(items.get(i)).equals(name)) {
                selectRow(i);
                return;
            }
        }
    }

    /** Number of entries currently shown (used by tests). */
    final int entryCount() {
        return items.size();
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

    /** Serializes the whole library to JSON (for export). */
    protected abstract String toJson(List<E> entries);

    /** Parses a JSON export back into entries; returns an empty list on failure. */
    protected abstract List<E> fromJson(String json);

    // ----------------------------------------------------------------------- editor actions

    private void newEntry() {
        openEditor(null);
    }

    private void editSelected() {
        if (selectedIndex >= 0 && selectedIndex < items.size()) {
            openEditor(items.get(selectedIndex));
        }
    }

    private void deleteCurrent() {
        if (selectedIndex < 0 || selectedIndex >= items.size()) {
            return;
        }
        var error = removeByName(nameOf(items.get(selectedIndex)));
        if (error != null) {
            JOptionPane.showMessageDialog(this, error, "Delete failed",
                JOptionPane.ERROR_MESSAGE);
            return;
        }
        reload();
    }

    /**
     * Opens the modal editor dialog, pre-filled from {@code entry} (a fresh empty form when
     * {@code null}). Confirming persists immediately and selects the entry in the list.
     */
    private void openEditor(@Nullable E entry) {
        if (form == null) {
            return;
        }
        final var editing = entry == null ? null : nameOf(entry);
        populateForm(entry);

        var owner = SwingUtilities.getWindowAncestor(this);
        var dialog = new JDialog(owner,
            (entry == null ? "New " : "Edit ") + singular(title),
            Dialog.ModalityType.APPLICATION_MODAL);
        var status = new JLabel(" ");
        status.setForeground(Color.RED);

        var ok = new JButton("OK");
        var cancel = new JButton("Cancel");
        ok.addActionListener(ev -> {
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
            if (editing != null && !editing.equals(newName)) {
                removeByName(editing);
            }
            dialog.dispose();
            reload();
            selectByName(newName);
        });
        cancel.addActionListener(ev -> dialog.dispose());
        dialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
        dialog.getRootPane().setDefaultButton(ok);

        var buttons = new JPanel(new FlowLayout(FlowLayout.RIGHT, 4, 0));
        buttons.add(ok);
        buttons.add(cancel);
        var south = new JPanel(new BorderLayout(4, 0));
        south.add(status, BorderLayout.CENTER);
        south.add(buttons, BorderLayout.EAST);

        var content = dialog.getContentPane();
        content.add(form, BorderLayout.CENTER);
        content.add(south, BorderLayout.SOUTH);
        dialog.pack();
        dialog.setLocationRelativeTo(owner);
        dialog.setVisible(true);
    }

    private void exportLibrary() {
        var chooser = new JFileChooser();
        chooser.setDialogTitle("Export " + title.toLowerCase());
        chooser.setFileFilter(new FileNameExtensionFilter("JSON files", "json"));
        if (chooser.showSaveDialog(this) != JFileChooser.APPROVE_OPTION) {
            return;
        }
        var file = chooser.getSelectedFile();
        if (file != null && !file.getName().toLowerCase().endsWith(".json")) {
            file = new File(file.getParentFile(), file.getName() + ".json");
        }
        try {
            Files.writeString(file.toPath(), toJson(items), StandardCharsets.UTF_8);
            JOptionPane.showMessageDialog(this,
                "Exported " + items.size() + " " + title.toLowerCase() + " to " + file);
        } catch (IOException ex) {
            JOptionPane.showMessageDialog(this, "Export failed: " + ex.getMessage(),
                "Export failed", JOptionPane.ERROR_MESSAGE);
        }
    }

    private void importLibrary() {
        var chooser = new JFileChooser();
        chooser.setDialogTitle("Import " + title.toLowerCase());
        chooser.setFileFilter(new FileNameExtensionFilter("JSON files", "json"));
        if (chooser.showOpenDialog(this) != JFileChooser.APPROVE_OPTION) {
            return;
        }
        List<E> imported;
        try {
            imported = fromJson(
                Files.readString(chooser.getSelectedFile().toPath(), StandardCharsets.UTF_8));
        } catch (IOException ex) {
            JOptionPane.showMessageDialog(this, "Import failed: " + ex.getMessage(),
                "Import failed", JOptionPane.ERROR_MESSAGE);
            return;
        }
        if (imported.isEmpty()) {
            JOptionPane.showMessageDialog(this,
                "The file contains no valid " + title.toLowerCase() + ".");
            return;
        }
        reload();
        int added = 0;
        int updated = 0;
        int skipped = 0;
        for (var e : imported) {
            var existed = items.stream().anyMatch(cur -> nameOf(cur).equals(nameOf(e)));
            var error = store(e);
            if (error != null) {
                skipped++;
            } else if (existed) {
                updated++;
            } else {
                added++;
            }
        }
        reload();
        var summary = "Imported " + (added + updated) + " of " + imported.size() + " "
            + title.toLowerCase() + " (" + added + " new, " + updated + " updated).";
        if (skipped > 0) {
            summary += "\n" + skipped + " entries were invalid and skipped.";
        }
        JOptionPane.showMessageDialog(this, summary);
    }

    private void selectRow(int index) {
        for (int i = 0; i < rows.size(); i++) {
            rows.get(i).setSelected(i == index);
        }
        selectedIndex = index;
        updateButtonState();
    }

    /** "Prompts" → "Prompt", "Skills" → "Skill" for dialog titles. */
    private static String singular(String description) {
        return description.endsWith("s") ? description.substring(0, description.length() - 1)
                : description;
    }

    // --------------------------------------------------------------------------- list entries

    /**
     * One entry of the list: the name in bold with the description (if any) below it. Single clicks
     * select the entry, double clicks open the editor dialog.
     */
    private final class EntryRow extends JPanel {
        private final E entry;
        private final int index;
        private final JLabel nameLabel;
        private final @Nullable JLabel descriptionLabel;

        EntryRow(E entry, int index) {
            this.entry = entry;
            this.index = index;
            setOpaque(true);
            setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
            setBorder(BorderFactory.createCompoundBorder(
                BorderFactory.createMatteBorder(0, 0, 1, 0,
                    separatorColor()),
                BorderFactory.createEmptyBorder(6, 10, 6, 10)));

            nameLabel = new JLabel(nameOf(entry));
            nameLabel.setFont(nameLabel.getFont().deriveFont(Font.BOLD));
            nameLabel.setBorder(BorderFactory.createEmptyBorder(0, 0, 2, 0));
            addAligned(nameLabel);

            var description = descriptionOf(entry);
            if (description != null && !description.isBlank()) {
                descriptionLabel = new JLabel(description);
                addAligned(descriptionLabel);
            } else {
                descriptionLabel = null;
            }

            addMouseListener(new MouseAdapter() {
                @Override
                public void mouseClicked(MouseEvent e) {
                    selectRow(index);
                    if (e.getClickCount() == 2) {
                        openEditor(entry);
                    }
                }
            });
            setSelected(false);
        }

        private void addAligned(JComponent component) {
            component.setAlignmentX(Component.LEFT_ALIGNMENT);
            add(component);
        }

        void setSelected(boolean selected) {
            setBackground(selected ? UIManager.getColor("Table.selectionBackground")
                    : UIManager.getColor("Panel.background"));
            nameLabel.setForeground(
                selected ? UIManager.getColor("Table.selectionForeground") : null);
            if (descriptionLabel != null) {
                descriptionLabel.setForeground(selected
                        ? UIManager.getColor("Table.selectionForeground")
                        : UIManager.getColor("Label.disabledForeground"));
            }
        }

        private static Color separatorColor() {
            var color = UIManager.getColor("Separator.foreground");
            return color != null ? color : Color.GRAY;
        }
    }
}
