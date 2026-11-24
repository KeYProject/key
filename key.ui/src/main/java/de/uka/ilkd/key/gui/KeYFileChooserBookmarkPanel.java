/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.*;
import java.io.File;
import java.util.*;
import java.util.List;
import javax.swing.*;
import javax.swing.filechooser.FileFilter;

import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

import org.key_project.ui.util.DefaultListModel;
import org.key_project.ui.util.SortedDefaultListModel;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * This is a Panel used as accessory for the JFileChooser.
 * <p>
 * This panel allows the user to save, delete and jump to their bookmarked folders. It additionally
 * lists the folders of recently opened files below the bookmarks; these recent entries are derived
 * from the recent-files list and are not stored as bookmarks.
 * <p>
 * The bookmarks are stored as preferences inside {@link ViewSettings}
 *
 * @author Jonas Klamroth
 * @author weigl
 * @see ViewSettings#getFolderBookmarks()
 */
public class KeYFileChooserBookmarkPanel extends JPanel {
    private final @NonNull JFileChooser chooser;

    private final ViewSettings viewSettings =
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();

    private final DefaultListModel<BookmarkEntry> bookmarks =
        new SortedDefaultListModel<>(Comparator.comparing(BookmarkEntry::temporary)
                .thenComparing(entry -> entry.folder().getAbsolutePath()));
    private final JList<BookmarkEntry> listBookmarks = new JList<>(bookmarks);


    private final KeyAction actionAddBookmark = new AddBookmarkAction();
    private final KeyAction actionRemoveBookmark = new RemoveBookmarkAction();
    private final KeyAction actionExternalAddBookmark = new AddExternalBookmarkAction();

    /**
     * Creates a bookmark panel and binds it to the given {@code chooser}.
     *
     * @param chooser non null {@link JFileChooser}
     */
    public KeYFileChooserBookmarkPanel(@NonNull JFileChooser chooser) {
        this(chooser, null);
    }

    /**
     * Creates a bookmark panel and binds it to the given {@code chooser}. Folders of the given
     * recent files are displayed after the user-managed bookmarks.
     *
     * @param chooser non null {@link JFileChooser}
     * @param recentFiles recent files whose folders should be offered, or {@code null}
     */
    public KeYFileChooserBookmarkPanel(@NonNull JFileChooser chooser,
            @Nullable List<File> recentFiles) {
        this.chooser = chooser;

        // listen for current directory of the file chooser
        chooser.addPropertyChangeListener(JFileChooser.DIRECTORY_CHANGED_PROPERTY,
            e -> selectFolder(chooser.getCurrentDirectory()));

        setLayout(new BorderLayout(5, 5));
        setBorder(BorderFactory.createTitledBorder("Bookmarks:"));
        createPane();
        loadBookmarks(recentFiles);
    }

    private void createPane() {
        JScrollPane scrollPane = new JScrollPane(listBookmarks);
        scrollPane.setPreferredSize(new Dimension(250, 250));
        add(scrollPane);

        listBookmarks.setCellRenderer(new BookmarkRenderer());
        listBookmarks.addKeyListener(new KeyAdapter() {
            @Override
            public void keyPressed(KeyEvent e) {
                if (e.getKeyCode() == KeyEvent.VK_ENTER) {
                    setBookmark();
                }
            }
        });

        listBookmarks.addMouseListener(new MouseAdapter() {
            @Override
            public void mouseClicked(MouseEvent e) {
                if (e.getClickCount() == 2) {
                    setBookmark();
                }
            }
        });

        JPanel pSouth = new JPanel();
        pSouth.add(new JButton(actionAddBookmark));
        pSouth.add(new JButton(actionExternalAddBookmark));
        pSouth.add(new JButton(actionRemoveBookmark));
        add(pSouth, BorderLayout.SOUTH);
    }

    private void setBookmark() {
        BookmarkEntry entry = listBookmarks.getSelectedValue();
        if (entry != null) {
            chooser.setCurrentDirectory(entry.folder());
        }
    }

    private void selectFolder(@Nullable File folder) {
        if (folder == null) {
            return;
        }
        for (int i = 0; i < bookmarks.size(); i++) {
            if (sameFolder(bookmarks.get(i).folder(), folder)) {
                listBookmarks.setSelectedIndex(i);
                listBookmarks.ensureIndexIsVisible(i);
                return;
            }
        }
    }

    /**
     * Returns an absolute, normalized form of the given file.
     *
     * @param file the file to normalize
     * @return the normalized file
     */
    static File normalize(File file) {
        return file.toPath().toAbsolutePath().normalize().toFile();
    }

    private static boolean sameFolder(File first, File second) {
        return normalize(first).equals(normalize(second));
    }

    private void loadBookmarks(@Nullable List<File> recentFiles) {
        Map<File, BookmarkEntry> map = new HashMap<>();
        viewSettings.getFolderBookmarks()
                .stream().map(File::new).map(KeYFileChooserBookmarkPanel::normalize)
                .forEach(it -> map.put(it, new BookmarkEntry(it, 0)));

        if (recentFiles != null) {
            for (File it : recentFiles) {
                it = normalize(it);
                if (!map.containsKey(it)) {
                    map.put(it, new BookmarkEntry(it, 1));
                }
            }
        }

        File cwd = normalize(new File("."));
        if (!map.containsKey(cwd)) {
            map.put(cwd, new BookmarkEntry(cwd, 2));
        }

        var seq = new ArrayList<>(map.values());
        bookmarks.addAll(seq);
    }

    private void saveBookmarks() {
        List<String> newMarks = new ArrayList<>();
        for (int i = 0; i < bookmarks.size(); i++) {
            BookmarkEntry entry = bookmarks.get(i);
            if (entry.temporary() == 0) {
                newMarks.add(normalize(entry.folder()).getAbsolutePath());
            }
        }
        viewSettings.setFolderBookmarks(newMarks);
    }

    private void addBookmark(File folder) {
        folder = normalize(folder);
        if (findBookmark(folder) >= 0) {
            return;
        }
        removeRecentEntry(folder);
        bookmarks.addElement(new BookmarkEntry(folder, 0));
        saveBookmarks();
    }

    private int findBookmark(File folder) {
        for (int i = 0; i < bookmarks.size(); i++) {
            BookmarkEntry entry = bookmarks.get(i);
            if (entry.temporary() == 0 && sameFolder(entry.folder(), folder)) {
                return i;
            }
        }
        return -1;
    }

    /**
     * Removes a displayed recent folder if the same folder is added as a bookmark.
     */
    private void removeRecentEntry(File folder) {
        for (int i = bookmarks.size() - 1; i >= 0; i--) {
            BookmarkEntry entry = bookmarks.get(i);
            if (entry.temporary() > 0 && sameFolder(entry.folder(), folder)) {
                bookmarks.removeElementAt(i);
            }
        }
    }

    /**
     * An entry in the bookmark list.
     *
     * @param folder the folder to navigate to
     * @param temporary whether this entry was derived from the recent-files list and is therefore
     *        not a user-managed bookmark
     */
    private record BookmarkEntry(File folder, int temporary) {
    }

    private static class BookmarkRenderer implements ListCellRenderer<BookmarkEntry> {
        private static final int LIMIT = 50;
        private final DefaultListCellRenderer renderer = new DefaultListCellRenderer();
        private final Font baseFont = renderer.getFont();

        private String toString(File file) {
            StringBuilder sb = new StringBuilder();
            do {
                sb.insert(0, file.getName());
                file = file.getParentFile();
                if (file != null) {
                    sb.insert(0, '/');
                }
            } while (file != null && sb.length() < LIMIT);
            if (file != null) {
                sb.insert(0, '…');
            }
            return sb.toString();
        }

        @Override
        public Component getListCellRendererComponent(JList<? extends BookmarkEntry> list,
                BookmarkEntry value, int index, boolean isSelected, boolean cellHasFocus) {
            File folder = value.folder();
            String val;
            if (folder.getAbsolutePath().length() <= LIMIT) {
                val = folder.getAbsolutePath();
            } else {
                val = toString(folder);
            }
            if (value.temporary() == 1) {
                val += " (recently used)";
            }

            if (value.temporary() == 2) {
                val += " (cwd)";
            }

            Component component = renderer.getListCellRendererComponent(list, val, index,
                isSelected, cellHasFocus);
            component.setFont(value.temporary() > 0 ? baseFont.deriveFont(Font.ITALIC) : baseFont);
            return component;
        }
    }

    private class AddBookmarkAction extends KeyAction {
        AddBookmarkAction() {
            setIcon(IconFactory.plus(16));
            setTooltip("Adds the current directory to the bookmarks.");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            File toAdd = chooser.getCurrentDirectory();
            if (toAdd != null) {
                addBookmark(toAdd);
            }
        }
    }

    private class AddExternalBookmarkAction extends KeyAction {
        AddExternalBookmarkAction() {
            setIcon(IconFactory.PLUS_SQUARED.get(16));
            setTooltip("Opens a new file selection dialog to select a new bookmark.");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            JFileChooser fc = new JFileChooser(chooser.getCurrentDirectory());
            FileFilter ff = new FileFilter() {
                @Override
                public boolean accept(File pathname) {
                    return pathname.isDirectory();
                }

                @Override
                public String getDescription() {
                    return "A directory to add to the bookmarks";
                }
            };
            fc.setFileFilter(ff);
            fc.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
            int res = fc.showOpenDialog(null);
            if (res == JFileChooser.APPROVE_OPTION) {
                addBookmark(fc.getSelectedFile());
            }
        }
    }

    private class RemoveBookmarkAction extends KeyAction {
        RemoveBookmarkAction() {
            setName("");
            setIcon(IconFactory.minus(16));
            setTooltip("Removes the current selected bookmark from the list.");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            int selected = listBookmarks.getSelectedIndex();
            if (selected >= 0 && bookmarks.get(selected).temporary() == 0) {
                bookmarks.removeElementAt(selected);
                saveBookmarks();
            }
        }
    }
}
