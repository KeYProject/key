package de.uka.ilkd.key.gui;

import javax.swing.*;
import javax.swing.filechooser.FileFilter;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.prefs.Preferences;
import java.util.stream.Collectors;

/**
 * Created by jklamroth on 12/6/18.
 *
 * This is a Panel used as Accessory for the KeYFileChooser which allows to
 * save Bookmarks which may be used as shortcuts to directories often used.
 *
 * The bookmarks are stored as preferences.
 */
public class KeYFileChooserBookmarkPanel extends JPanel implements PropertyChangeListener {
    private final KeYFileChooser chooser;
    private JPanel bookmarkPanel = new JPanel(new GridBagLayout());
    private List<File> bookmarks = new ArrayList<>();
    private List<JToggleButton> buttons = new ArrayList<>();

    public KeYFileChooserBookmarkPanel(KeYFileChooser chooser) {
        super(new GridBagLayout());
        this.chooser = chooser;
        createPane();
    }

    private void createPane() {
        loadBookmarks();
        for (File f : bookmarks) {
            addBookmarkButton(f);
        }

        JScrollPane scrollPane = new JScrollPane(bookmarkPanel);
        scrollPane.setPreferredSize(new Dimension(214, 250));
        scrollPane.setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER);
        GridBagConstraints c = new GridBagConstraints();
        c.gridx = 0;
        c.gridy = 0;
        c.gridwidth = 2;
        c.fill = GridBagConstraints.BOTH;
        c.insets = new Insets(0, 10, 0, 0);
        this.add(scrollPane, c);
        JButton addButton = new JButton("+");
        addButton.addActionListener(e -> createBookmark());
        JButton removeButton = new JButton("-");
        removeButton.addActionListener(e -> removeCurrentBookmark());
        c = new GridBagConstraints();
        c.gridx = 0;
        c.gridy = this.getComponentCount();
        c.fill = GridBagConstraints.HORIZONTAL;
        c.insets = new Insets(20, 10, 0, 0);
        addButton.setPreferredSize(new Dimension(107, 25));
        this.add(addButton, c);
        c = new GridBagConstraints();
        c.gridx = 1;
        c.gridy = this.getComponentCount() - 1;
        c.fill = GridBagConstraints.HORIZONTAL;
        c.insets = new Insets(20, 0, 0, 0);
        removeButton.setPreferredSize(new Dimension(107, 25));
        this.add(removeButton, c);
        this.revalidate();
        this.repaint();
    }

    private void loadBookmarks() {
        String saveString = Preferences.userRoot().node(this.getUIClassID()).get("bookmarks", null);
        if(saveString != null) {
            String[] bookmarkStrings = saveString.split(";");
            for(String s : bookmarkStrings) {
                bookmarks.add(new File(s));
            }
        } else {
            loadDefaultBookmarks();
        }
    }

    private void loadDefaultBookmarks() {
        bookmarks.add(new File(System.getProperty("user.home")));
    }

    private void createBookmark() {
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
        int res = fc.showOpenDialog(this);
        if (res == JFileChooser.APPROVE_OPTION) {
            addBookmark(fc.getSelectedFile());
        }
        assert(buttons.size() == bookmarks.size());
    }

    private void removeCurrentBookmark() {
        JToggleButton selected = null;
        for (JToggleButton b : buttons) {
            if (b.isSelected()) {
                selected = b;
                break;
            }
        }
        if (selected != null) {
            int idx = buttons.indexOf(selected);
            buttons.remove(selected);
            bookmarkPanel.remove(selected);
            bookmarks.remove(idx);
            saveBookmarks();
            this.revalidate();
            this.repaint();
        }
        assert(buttons.size() == bookmarks.size());
    }

    private void addBookmark(File f) {
        bookmarks.add(f);
        addBookmarkButton(f);
    }

    private void addBookmarkButton(File f) {
        JToggleButton button = new JToggleButton(f.getName());
        button.setToolTipText(f.getAbsolutePath());
        button.setForeground(Color.BLUE);
        button.addActionListener(e -> {
            chooser.setCurrentDirectory(f);
        });
        button.setPreferredSize(new Dimension(200, 25));
        buttons.add(button);
        GridBagConstraints c = new GridBagConstraints();
        c.fill = GridBagConstraints.HORIZONTAL;
        c.gridx = 0;
        c.gridy = bookmarkPanel.getComponentCount();
        bookmarkPanel.add(button, c);
        saveBookmarks();
        this.revalidate();
        this.repaint();
    }

    public void propertyChange(PropertyChangeEvent e) {
        String prop = e.getPropertyName();
        if (JFileChooser.DIRECTORY_CHANGED_PROPERTY.equals(prop)) {
            File selected = chooser.getCurrentDirectory();
            for (int i = 0; i < buttons.size(); ++i) {
                if (bookmarks.get(i).equals(selected)) {
                    buttons.get(i).setSelected(true);
                } else {
                    buttons.get(i).setSelected(false);
                }
            }
        }
        this.revalidate();
        this.repaint();
    }

    private void saveBookmarks() {
        String saveString = bookmarks.stream().map(file -> file.getAbsolutePath()).collect(Collectors.joining(";"));
        Preferences.userRoot().node(this.getUIClassID()).put("bookmarks", saveString);
    }

}
