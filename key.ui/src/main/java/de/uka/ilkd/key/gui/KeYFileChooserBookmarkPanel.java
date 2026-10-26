/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.*;
import java.io.File;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;
import javax.swing.*;
import javax.swing.filechooser.FileFilter;

import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;

/**
 * This is a Panel used as accessory for the JFileChooser.
 * <p>
 * This panel allows the user to save, delete and jump to their bookmarked folders.
 * <p>
 * The bookmarks are stored as preferences inside {@link ViewSettings}
 *
 * @author Jonas Klamroth
 * @author weigl
 * @see ViewSettings#getFolderBookmarks()
 */
@NullMarked
public class KeYFileChooserBookmarkPanel extends JPanel {
    private final @NonNull JFileChooser chooser;

    private final ViewSettings viewSettings =
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();

    private final DefaultListModel<File> bookmarks = new DefaultListModel<>();
    private final JList<File> listBookmarks = new JList<>(bookmarks);

    private final KeyAction actionAddBookmark = new AddBookmarkAction();
    private final KeyAction actionRemoveBookmark = new RemoveBookmarkAction();
    private final KeyAction actionExternalAddBookmark = new AddExternalBookmarkAction();

    /**
     * Creates a bookmark panel and bind it to the given {@code chooser}.
     *
     * @param chooser non null {@link JFileChooser}
     */
    /**
     * The ctor configures the panel and its children while the receiver is still under
     * initialization (EISOP initialization check); the effects only take place after construction
     * completes, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public KeYFileChooserBookmarkPanel(@NonNull JFileChooser chooser) {
        this.chooser = chooser;

        // listen for current directory of the file chooser
        chooser.addPropertyChangeListener(JFileChooser.DIRECTORY_CHANGED_PROPERTY, e -> {
            File selected = chooser.getCurrentDirectory();
            if (selected == null) {
                // the file chooser always has a current directory
                throw new NullPointerException("No current directory available.");
            }
            listBookmarks.setSelectedValue(selected, true);
        });

        setLayout(new BorderLayout(5, 5));
        setBorder(BorderFactory.createTitledBorder("Bookmarks:"));
        createPane();
        loadBookmarks();
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
        if (listBookmarks.getSelectedValue() != null) {
            chooser.setCurrentDirectory(listBookmarks.getSelectedValue());
        }
    }

    private void loadBookmarks() {
        viewSettings.getFolderBookmarks().forEach(it -> bookmarks.addElement(new File(it)));
    }

    private void saveBookmarks() {
        List<String> newMarks = new ArrayList<>();
        Enumeration<File> iter = bookmarks.elements();
        while (iter.hasMoreElements()) {
            newMarks.add(iter.nextElement().getAbsolutePath());
        }
        viewSettings.setFolderBookmarks(newMarks);
    }

    private static class BookmarkRenderer implements ListCellRenderer<File> {
        /**
         * Character limit for entries. We try to keep folder entries shorter than the defined
         * values
         */
        private static final int LIMIT = 25;
        private final DefaultListCellRenderer renderer = new DefaultListCellRenderer();

        private String toString(File file) {
            StringBuilder sb = new StringBuilder();
            File current = file;
            do {
                sb.insert(0, current.getName());
                current = current.getParentFile();
                if (current != null) {
                    sb.insert(0, '/');
                }
            } while (current != null && sb.length() < LIMIT);
            if (current != null) {
                sb.insert(0, '…');
            }
            return sb.toString();
        }

        @Override
        public Component getListCellRendererComponent(JList<? extends File> list, File value,
                int index, boolean isSelected, boolean cellHasFocus) {
            String val;
            if (value.getAbsolutePath().length() <= LIMIT) {
                val = value.getAbsolutePath();
            } else {
                val = toString(value);
            }
            return renderer.getListCellRendererComponent(list, val, index, isSelected,
                cellHasFocus);
        }
    }

    private class AddBookmarkAction extends KeyAction {
        /**
         * The action-configuration setters are called on {@code this} while the receiver is still
         * under initialization (EISOP initialization check); safe here, suppressed with a scoped
         * key.
         */
        @SuppressWarnings("nullness:method.invocation.invalid")
        AddBookmarkAction() {
            setIcon(IconFactory.plus(16));
            setTooltip("Adds the current directory to the bookmarks.");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            File toAdd = chooser.getCurrentDirectory();
            if (toAdd != null) {
                final int index = bookmarks.indexOf(toAdd);
                if (index >= 0) {
                    // already in the list
                    return;
                }
                bookmarks.addElement(toAdd);
                saveBookmarks();
            }
        }
    }

    private class AddExternalBookmarkAction extends KeyAction {
        /**
         * The action-configuration setters are called on {@code this} while the receiver is still
         * under initialization (EISOP initialization check); safe here, suppressed with a scoped
         * key.
         */
        @SuppressWarnings("nullness:method.invocation.invalid")
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
                File toAdd = fc.getSelectedFile();
                if (toAdd == null) {
                    // a directory approval always yields a selection
                    throw new NullPointerException("No selected file available.");
                }
                final int index = bookmarks.indexOf(toAdd);
                if (index >= 0) {
                    // already in the list
                    return;
                }
                bookmarks.addElement(toAdd);
                saveBookmarks();
            }
        }
    }

    private class RemoveBookmarkAction extends KeyAction {
        /**
         * The action-configuration setters are called on {@code this} while the receiver is still
         * under initialization (EISOP initialization check); safe here, suppressed with a scoped
         * key.
         */
        @SuppressWarnings("nullness:method.invocation.invalid")
        RemoveBookmarkAction() {
            setName("");
            setIcon(IconFactory.minus(16));
            setTooltip("Removes the current selected bookmark from the list.");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            int selected = listBookmarks.getSelectedIndex();
            if (selected >= 0) {
                bookmarks.removeElementAt(selected);
                saveBookmarks();
            }
        }
    }
}
