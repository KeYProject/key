/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Desktop;
import java.awt.Dialog;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.GraphicsEnvironment;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import javax.swing.*;
import javax.swing.filechooser.FileNameExtensionFilter;

import de.uka.ilkd.key.gui.settings.SimpleSettingsPanel;

import org.jspecify.annotations.Nullable;

/**
 * Lightweight editor for a file-backed user library (prompts or skills) shown as its own
 * settings-tree node below "LLM Settings" (see {@code LlmExtension.LlmSettingsProvider}). The
 * entries are the Markdown files of the library; they are listed by name and description, and
 * edited as regular files: {@code New} only asks for the file name and creates a template file
 * with prefilled front matter, {@code Edit} opens the file in the system editor (falling back to
 * a plain text dialog when no desktop integration is available). Entries are deleted with
 * {@code Delete}, and the whole library can be exported to or imported from a ZIP archive of
 * Markdown files (one {@code <name>.md} per entry, see {@link LibraryZip}).
 * <p>
 * Below the list the library's search path is editable: an ordered list of directories holding
 * the files (first occurrence of a name wins, new files are created in the first directory).
 * {@code Add directory...} opens a directory chooser, {@code Add path...} allows arbitrary
 * entries using {@code ~} (home directory), {@code $(pwd)} and relative paths (working
 * directory); an empty list selects the default directory, which is then shown (and protected
 * from removal) as a pseudo-entry.
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
    private final DefaultListModel<String> searchPathModel = new DefaultListModel<>();
    private final JList<String> searchPathList = new JList<>(searchPathModel);
    private final JTextArea searchPathHint = new JTextArea();
    private final JButton btnRemoveSearchDir = new JButton("Remove");
    private int selectedIndex = -1;

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
        actions.add(button("Reload", this::reload));
        actions.add(button("Export...", this::exportLibrary));
        actions.add(button("Import...", this::importLibrary));

        var south = new JPanel();
        south.setLayout(new BoxLayout(south, BoxLayout.Y_AXIS));
        south.add(buildSearchPathPanel());
        south.add(actions);

        pCenter.add(listBox, BorderLayout.CENTER);
        pCenter.add(south, BorderLayout.SOUTH);
        updateButtonState();
    }

    private static JButton button(String text, Runnable action) {
        var b = new JButton(text);
        b.addActionListener(e -> action.run());
        return b;
    }

    /**
     * The search path editor: a list of directories (with an explicit row for the effective
     * default directory when nothing is configured), buttons to add/remove directories and a
     * wrapping explanation of the search semantics.
     */
    private JComponent buildSearchPathPanel() {
        searchPathList.setVisibleRowCount(6);
        searchPathList.addListSelectionListener(e -> updateRemoveSearchDirState());
        btnRemoveSearchDir.addActionListener(e -> removeSearchDir());

        var buttons = new JPanel(new FlowLayout(FlowLayout.LEFT, 4, 0));
        buttons.add(button("Add directory...", this::addSearchDir));
        buttons.add(button("Add path...", this::addSearchPathEntry));
        buttons.add(btnRemoveSearchDir);

        // a wrapping text area: a JLabel would overflow the panel with its single long line
        searchPathHint.setEditable(false);
        searchPathHint.setFocusable(false);
        searchPathHint.setOpaque(false);
        searchPathHint.setLineWrap(true);
        searchPathHint.setWrapStyleWord(true);
        searchPathHint.setColumns(66);
        searchPathHint.setForeground(UIManager.getColor("Label.disabledForeground"));
        searchPathHint.setBorder(BorderFactory.createEmptyBorder(4, 10, 4, 10));

        var scroll = new JScrollPane(searchPathList);
        scroll.setBorder(BorderFactory.createEmptyBorder());

        var panel = new JPanel(new BorderLayout(0, 4));
        panel.setBorder(BorderFactory.createTitledBorder("Search path"));
        panel.add(buttons, BorderLayout.NORTH);
        panel.add(scroll, BorderLayout.CENTER);
        panel.add(searchPathHint, BorderLayout.SOUTH);
        return panel;
    }

    /** Enables "Remove" only for a real, removable entry (not the default-directory row). */
    private void updateRemoveSearchDirState() {
        var dirs = searchDirs();
        int index = searchPathList.getSelectedIndex();
        btnRemoveSearchDir.setEnabled(!dirs.isEmpty() && index >= 0 && index < dirs.size());
    }

    private void updateButtonState() {
        boolean hasSelection = selectedIndex >= 0 && selectedIndex < items.size();
        btnEdit.setEnabled(hasSelection);
        btnDelete.setEnabled(hasSelection);
    }

    // ------------------------------------------------------------------ for subclasses

    /** Reloads the list (and the search path) from the library and clears the selection. */
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
        refreshSearchPath();
        updateButtonState();
    }

    /** Prefix of the pseudo-entry shown when no directory is configured. */
    private static final String DEFAULT_DIR_PREFIX = "(default directory)  ";

    private void refreshSearchPath() {
        searchPathModel.clear();
        var dirs = searchDirs();
        if (dirs.isEmpty()) {
            // the effective default directory, not removable
            searchPathModel.addElement(DEFAULT_DIR_PREFIX + defaultDirectory());
        }
        dirs.forEach(searchPathModel::addElement);
        updateRemoveSearchDirState();
        updateSearchPathHint();
    }

    private void updateSearchPathHint() {
        if (searchDirs().isEmpty()) {
            searchPathHint.setText(
                "Only the default directory is searched: " + defaultDirectory() + ".\n"
                    + "Click \u201CAdd directory...\u201D to search your own folders as well"
                    + " (or \u201CAdd path...\u201D for a location using ~ or $(pwd)).");
        } else {
            searchPathHint.setText("Search order: the first occurrence of a name wins and new"
                + " files are created in the first directory. \u201C~\u201D is the home"
                + " directory; \u201C$(pwd)\u201D and relative paths are resolved against the"
                + " working directory.");
        }
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

    /** Persists an element (create or replace); returns {@code null} on success or an error. */
    protected abstract String store(E e);

    /** Deletes the entry with the given name; returns {@code null} on success or an error. */
    protected abstract String removeByName(String name);

    /**
     * Creates a new entry file for the given name, prefilled with a template (front matter with
     * the name and a placeholder body). Returns {@code null} on success or an error message.
     */
    protected abstract String createEntry(String name);

    /** The file backing the entry with the given name, or {@code null} when it has none. */
    protected abstract @Nullable Path fileOf(String name);

    /** Serializes one entry to its Markdown document (for the ZIP export). */
    protected abstract String toMarkdown(E e);

    /** Parses one entry from its Markdown document; {@code null} when the entry is invalid. */
    protected abstract @Nullable E fromMarkdown(String markdown);

    /** The raw search path directories of the library (as configured, not expanded). */
    protected abstract List<String> searchDirs();

    /** Persists the search path directories of the library. */
    protected abstract void setSearchDirs(List<String> dirs);

    /** The default directory used when the search path is empty (for the hint text). */
    protected abstract Path defaultDirectory();

    // ------------------------------------------------------------- search path actions

    /** Opens a directory chooser and appends the chosen directory to the search path. */
    private void addSearchDir() {
        var chooser = new JFileChooser();
        chooser.setDialogTitle("Add " + title.toLowerCase() + " directory");
        chooser.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
        chooser.setAcceptAllFileFilterUsed(false);
        if (chooser.showOpenDialog(this) != JFileChooser.APPROVE_OPTION) {
            return;
        }
        var dir = chooser.getSelectedFile();
        if (dir != null) {
            appendSearchEntry(dir.toPath().toString());
        }
    }

    /** Manual entry for search path locations using {@code ~}, {@code $(pwd)} or relative paths. */
    private void addSearchPathEntry() {
        var value = JOptionPane.showInputDialog(this,
            "Directory to search for " + title.toLowerCase() + ":\n"
                + "(\"~\" = home directory, \"$(pwd)\" = working directory)",
            "");
        if (value == null) {
            return;
        }
        value = value.strip();
        if (!value.isEmpty()) {
            appendSearchEntry(value);
        }
    }

    private void appendSearchEntry(String value) {
        var dirs = new ArrayList<>(searchDirs());
        if (!dirs.contains(value)) {
            dirs.add(value);
            setSearchDirs(dirs);
            reload();
        }
    }

    private void removeSearchDir() {
        var dirs = new ArrayList<>(searchDirs());
        int index = searchPathList.getSelectedIndex();
        if (dirs.isEmpty() || index < 0 || index >= dirs.size()) {
            return; // the default-directory pseudo-entry is not removable
        }
        dirs.remove(index);
        setSearchDirs(dirs);
        reload();
    }

    // ----------------------------------------------------------------------- editor actions

    /**
     * Asks for the file name of the new entry and creates a template file for it.
     */
    private void newEntry() {
        var name = JOptionPane.showInputDialog(this,
            "Name of the new " + singular(title).toLowerCase()
                + " (used as the file name and as the trigger):",
            "");
        if (name == null) {
            return;
        }
        name = name.strip();
        if (name.isEmpty()) {
            JOptionPane.showMessageDialog(this, "Please enter a name.",
                "New " + singular(title), JOptionPane.WARNING_MESSAGE);
            return;
        }
        var error = createEntry(name);
        if (error != null) {
            JOptionPane.showMessageDialog(this, error, "New " + singular(title),
                JOptionPane.ERROR_MESSAGE);
            return;
        }
        reload();
        selectByName(name);
    }

    /** Opens the file of the selected entry in the system editor (or a fallback dialog). */
    private void editSelected() {
        if (selectedIndex < 0 || selectedIndex >= items.size()) {
            return;
        }
        var name = nameOf(items.get(selectedIndex));
        var file = fileOf(name);
        if (file == null) {
            JOptionPane.showMessageDialog(this, "No file for '" + name + "' was found.",
                "Edit " + singular(title), JOptionPane.ERROR_MESSAGE);
            reload();
            return;
        }
        if (!openExternally(file)) {
            openTextDialog(file);
        }
    }

    /**
     * Opens {@code file} with the system's default text editor. Returns {@code false} when the
     * desktop integration is unavailable (headless, unsupported) or fails.
     */
    private static boolean openExternally(Path file) {
        if (GraphicsEnvironment.isHeadless() || !Desktop.isDesktopSupported()) {
            return false;
        }
        try {
            var desktop = Desktop.getDesktop();
            if (!desktop.isSupported(Desktop.Action.OPEN)) {
                return false;
            }
            desktop.open(file.toFile());
            return true;
        } catch (IOException | RuntimeException ex) {
            return false;
        }
    }

    /** Fallback editor: shows the raw Markdown document in a plain dialog and writes it back. */
    private void openTextDialog(Path file) {
        String content;
        try {
            content = Files.readString(file, StandardCharsets.UTF_8);
        } catch (IOException e) {
            JOptionPane.showMessageDialog(this, "Could not read " + file + ": " + e.getMessage(),
                "Edit " + singular(title), JOptionPane.ERROR_MESSAGE);
            return;
        }
        var area = new JTextArea(content, 24, 80);
        area.setFont(new Font(Font.MONOSPACED, Font.PLAIN, area.getFont().getSize()));
        area.setLineWrap(true);
        area.setWrapStyleWord(true);

        var owner = SwingUtilities.getWindowAncestor(this);
        var dialog =
            new JDialog(owner, "Edit " + file, Dialog.ModalityType.APPLICATION_MODAL);
        var save = new JButton("Save");
        save.addActionListener(ev -> {
            try {
                Files.writeString(file, area.getText(), StandardCharsets.UTF_8);
                dialog.dispose();
                reload();
            } catch (IOException ex) {
                JOptionPane.showMessageDialog(dialog,
                    "Could not write " + file + ": " + ex.getMessage(), "Save failed",
                    JOptionPane.ERROR_MESSAGE);
            }
        });
        var cancel = new JButton("Cancel");
        cancel.addActionListener(ev -> dialog.dispose());
        dialog.getRootPane().setDefaultButton(save);
        var buttons = new JPanel(new FlowLayout(FlowLayout.RIGHT, 4, 0));
        buttons.add(save);
        buttons.add(cancel);

        var contentPane = dialog.getContentPane();
        contentPane.add(new JScrollPane(area), BorderLayout.CENTER);
        contentPane.add(buttons, BorderLayout.SOUTH);
        dialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
        dialog.pack();
        dialog.setLocationRelativeTo(owner);
        dialog.setVisible(true);
    }

    private void deleteCurrent() {
        if (selectedIndex < 0 || selectedIndex >= items.size()) {
            return;
        }
        var name = nameOf(items.get(selectedIndex));
        var confirm = JOptionPane.showConfirmDialog(this,
            "Delete '" + name + "' from all search path directories?", "Delete " + singular(title),
            JOptionPane.YES_NO_OPTION, JOptionPane.QUESTION_MESSAGE);
        if (confirm != JOptionPane.YES_OPTION) {
            return;
        }
        var error = removeByName(name);
        if (error != null) {
            JOptionPane.showMessageDialog(this, error, "Delete failed",
                JOptionPane.ERROR_MESSAGE);
        }
        reload();
    }

    private void exportLibrary() {
        reload(); // pick up external changes before exporting
        var chooser = new JFileChooser();
        chooser.setDialogTitle("Export " + title.toLowerCase());
        chooser.setFileFilter(new FileNameExtensionFilter("ZIP archives", "zip"));
        if (chooser.showSaveDialog(this) != JFileChooser.APPROVE_OPTION) {
            return;
        }
        var file = chooser.getSelectedFile();
        if (file != null && !file.getName().toLowerCase().endsWith(".zip")) {
            file = new File(file.getParentFile(), file.getName() + ".zip");
        }
        var entries = new LinkedHashMap<String, String>();
        for (var e : items) {
            entries.put(nameOf(e) + ".md", toMarkdown(e));
        }
        try {
            LibraryZip.write(file.toPath(), entries);
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
        chooser.setFileFilter(new FileNameExtensionFilter("ZIP archives", "zip"));
        if (chooser.showOpenDialog(this) != JFileChooser.APPROVE_OPTION) {
            return;
        }
        List<E> imported = new ArrayList<>();
        try {
            for (var entry : LibraryZip.read(chooser.getSelectedFile().toPath()).entrySet()) {
                if (!entry.getKey().endsWith(".md")) {
                    continue; // only library documents, ignore everything else in the archive
                }
                var e = fromMarkdown(entry.getValue());
                if (e != null) {
                    imported.add(e);
                }
            }
        } catch (IOException ex) {
            JOptionPane.showMessageDialog(this, "Import failed: " + ex.getMessage(),
                "Import failed", JOptionPane.ERROR_MESSAGE);
            return;
        }
        if (imported.isEmpty()) {
            JOptionPane.showMessageDialog(this,
                "The archive contains no valid " + title.toLowerCase() + ".");
            return;
        }
        reload();
        var conflicts = imported.stream()
                .filter(e -> items.stream().anyMatch(cur -> nameOf(cur).equals(nameOf(e))))
                .toList();
        boolean overrideExisting = false;
        if (!conflicts.isEmpty()) {
            var confirm = JOptionPane.showConfirmDialog(this,
                conflicts.size() + " of the imported " + title.toLowerCase() + " already exist.\n"
                    + "\u201CYes\u201D overrides them, \u201CNo\u201D keeps the existing entries.",
                "Import " + title.toLowerCase(), JOptionPane.YES_NO_CANCEL_OPTION,
                JOptionPane.QUESTION_MESSAGE);
            if (confirm == JOptionPane.CANCEL_OPTION || confirm == JOptionPane.CLOSED_OPTION) {
                return;
            }
            overrideExisting = confirm == JOptionPane.YES_OPTION;
        }
        int added = 0;
        int updated = 0;
        int skipped = 0;
        for (var e : imported) {
            var existed = items.stream().anyMatch(cur -> nameOf(cur).equals(nameOf(e)));
            if (existed && !overrideExisting) {
                skipped++;
                continue;
            }
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
            summary += "\n" + skipped + " entries were skipped"
                + (overrideExisting ? " (invalid)." : " (kept existing).");
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
     * One entry of the list: the name in bold with the description (if any) below it. Single
     * clicks select the entry, double clicks open it for editing.
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
                        editSelected();
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
