package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.util.Pair;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.*;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;

/**
 * This class offers a mechanism to manage recent files; it adds the necessary menu items to a menu
 * or even can provide that menu itself. also it offers a way to read the recent files from a
 * java.util.Properties object and can store them again to a Properties object. This class is a
 * result of the fusion of the RecentFileBuffer and RecentFiles classes. It's not a Menu in
 * itself!!!
 *
 * @author Ute Platzer, with a lot of input from Volker Braun.
 */
public class RecentFileMenu {
    private static final Logger LOGGER = LoggerFactory.getLogger(RecentFileMenu.class);

    /**
     * The maximum number of recent files displayed.
     */
    private static final int MAX_RECENT_FILES = 8;

    /**
     * this is the maximal number of recent files.
     */
    private int maxNumberOfEntries;


    private final JMenu menu;

    /**
     * the actionListener to be notified of mouse-clicks or other actionevents on the menu items
     */
    private final ActionListener lissy;

    /**
     * recent files, unique by path
     */
    private final HashMap<String, RecentFileEntry> pathToRecentFile = new HashMap<>();
    /**
     * Mapping from menu item to entry
     */
    private final HashMap<JMenuItem, RecentFileEntry> menuItemToRecentFile;

    private RecentFileEntry mostRecentFile;

    /**
     * Create a new RecentFiles list.
     *
     * @param mediator Key mediator
     */
    public RecentFileMenu(final KeYMediator mediator) {
        this.menu = new JMenu("Recent Files");
        this.lissy = new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                String absPath = getAbsolutePath((JMenuItem) e.getSource());
                File file = new File(absPath);

                // special case proof bundles -> allow to select the proof to load
                if (ProofSelectionDialog.isProofBundle(file.toPath())) {
                    Path proofPath = ProofSelectionDialog.chooseProofToLoad(file.toPath());
                    if (proofPath == null) {
                        // canceled by user!
                        return;
                    } else {
                        mediator.getUI().loadProofFromBundle(file, proofPath.toFile());
                        return;
                    }
                } else {
                    mediator.getUI().loadProblem(file);
                }
            }
        };
        this.maxNumberOfEntries = MAX_RECENT_FILES;

        this.menuItemToRecentFile = new LinkedHashMap<>();

        menu.setEnabled(menu.getItemCount() != 0);
        menu.setIcon(IconFactory.recentFiles(16));

        load(PathConfig.getRecentFileStorage());
    }

    private void insertFirstEntry(RecentFileEntry entry) {
        menu.insert(entry.getMenuItem(), 0);
        mostRecentFile = entry;
    }

    private static void resolveDuplicate(RecentFileEntry entry, RecentFileEntry shorter) {
        while (entry.getName().endsWith(shorter.getName())
                && entry.getName().length() != shorter.getName().length()) {
            boolean secondCanBeMadeLonger = shorter.makeNameLonger();
            // break if we resolved the duplicate or neither one can be made longer
            if (!entry.getName().endsWith(shorter.getName())) {
                return;
            }
            if (!secondCanBeMadeLonger) {
                break;
            }
        }

        while (true) {
            boolean firstCanBeMadeLonger = entry.makeNameLonger();
            boolean secondCanBeMadeLonger = shorter.makeNameLonger();
            // break if we resolved the duplicate or neither one can be made longer
            if (!entry.getName().equals(shorter.getName())
                    || !(firstCanBeMadeLonger || secondCanBeMadeLonger)) {
                break;
            }
        }
    }

    private static void prepareForInsertionOf(
            HashMap<String, RecentFileEntry> pathToRecentFile,
            RecentFileEntry entry) {
        // Entry to add is always only a file name
        for (RecentFileEntry e : pathToRecentFile.values()) {
            if (e.getName().endsWith(entry.getName())) {
                resolveDuplicate(e, entry);
            }
        }
    }

    public static void main(String[] args) {
        // (Path, name after all insertions)
        var paths = Arrays.asList(
            new Pair<>(Paths.get("z", "a", "b", "c").toString(),
                Paths.get("z", "a", "b", "c").toString()),
            new Pair<>(Paths.get("a", "b", "c").toString(), Paths.get("a", "b", "c").toString()),
            new Pair<>(Paths.get("b", "b", "c").toString(), Paths.get("b", "b", "c").toString()),
            new Pair<>(Paths.get("z", "b", "b", "c").toString(),
                Paths.get("z", "b", "b", "c").toString()),
            new Pair<>(Paths.get("b", "c").toString(), Paths.get("b", "c").toString()),
            new Pair<>(Paths.get("b", "d").toString(), Paths.get("d").toString()),
            new Pair<>(Paths.get("x", "y").toString(), Paths.get("y").toString()));
        Random random = new Random(42);
        for (int i = 0; i < 1000; ++i) {
            Collections.shuffle(paths, random);
            var entries = new HashMap<String, RecentFileEntry>();
            for (Pair<String, String> pair : paths) {
                var e = new RecentFileEntry(pair.first);
                prepareForInsertionOf(entries, e);
                entries.put(e.getAbsolutePath(), e);
            }

            for (Pair<String, String> pair : paths) {
                if (!entries.get(pair.first).getName().equals(pair.second)) {
                    throw new IllegalStateException();
                }
            }
        }
    }

    /**
     * add path to the menu
     */
    private void addNewToModelAndView(final String path) {
        // do not add quick save location to recent files
        if (de.uka.ilkd.key.gui.actions.QuickSaveAction.QUICK_SAVE_PATH.endsWith(path))
            return;

        if (new File(path).exists()) {
            final RecentFileEntry entry = new RecentFileEntry(path);
            prepareForInsertionOf(pathToRecentFile, entry);
            this.pathToRecentFile.put(entry.getAbsolutePath(), entry);
            final JMenuItem item = entry.getMenuItem();
            menuItemToRecentFile.put(item, entry);
            item.addActionListener(lissy);

            insertFirstEntry(entry);
        }
    }

    /**
     *
     */
    private String getAbsolutePath(JMenuItem item) {
        return menuItemToRecentFile.get(item).getAbsolutePath();
    }

    /**
     * call this method to add a new file to the beginning of the RecentFiles list. If the path is
     * already part of the list, it will be moved to the first position. No more than a specified
     * maximum number of names will be allowed in the list, and additional names will be removed at
     * the end. (set the maximum number with the {@link #setMaxNumberOfEntries(int i)} method).
     *
     * @param path the path of the file.
     */
    public void addRecentFile(final String path) {
        // Add the path to the recentFileList:
        // check whether this path is already there
        LOGGER.debug("recentfilemenu: add file: {}", path);
        LOGGER.debug("recentfilemenu: at menu count: {}", menu.getItemCount());
        final RecentFileEntry existingEntry = pathToRecentFile.get(path);
        if (existingEntry != null) {
            menu.remove(existingEntry.getMenuItem());
            insertFirstEntry(existingEntry);
            return;
        }

        // if appropriate, remove the last entry.
        if (menu.getItemCount() == maxNumberOfEntries) {
            final JMenuItem item = menu.getItem(menu.getItemCount() - 1);
            final RecentFileEntry entry = menuItemToRecentFile.get(item);
            menuItemToRecentFile.remove(entry.getMenuItem());
            pathToRecentFile.remove(entry.getAbsolutePath());
            menu.remove(entry.getMenuItem());
        }
        addNewToModelAndView(path);
        menu.setEnabled(menu.getItemCount() != 0);
    }

    /**
     * specify the maximal number of recent files in the list. The default is MAX_RECENT_FILES
     */
    public void setMaxNumberOfEntries(int max) {
        if (maxNumberOfEntries > max && menu.getItemCount() > max) {
            for (int i = menu.getItemCount() - 1; i > max; i--) {
                menu.remove(i);
            }

        }
        this.maxNumberOfEntries = max;
    }

    /**
     * the menu where the recent files are kept. If the user didn't specify one in the constructor,
     * a new JMenu is created. It can be accessed via this method.
     */
    public JMenu getMenu() {
        return menu;
    }

    /**
     * read the recent file names from the properties object. the property names are expected to be
     * "RecentFile0" "RecentFile1" ...
     */
    public void load(Properties p) {
        int i = maxNumberOfEntries;
        String s;
        do {
            s = p.getProperty("RecentFile" + i);
            if (s != null)
                addRecentFile(s);
            i--;
        } while (i >= 0);
    }

    /**
     * Put the names of the recent Files into the properties object. The property names are
     * "RecentFile0" "RecentFile1" ... The values are fully qualified path names.
     */
    public void store(Properties p) {
        // if there's nothing to store:
        for (int i = 0; i < menu.getItemCount(); i++) {
            p.setProperty("RecentFile" + i, getAbsolutePath(menu.getItem(i)));
        }
    }

    /**
     * read the recent files from the given properties file
     */
    public final void load(String filename) {
        FileInputStream propStream = null;
        try {
            propStream = new FileInputStream(filename);
            Properties p = new Properties();
            p.load(propStream);
            Enumeration<?> e = p.propertyNames();
            while (e.hasMoreElements()) {
                String s = (String) e.nextElement();
                if (s.indexOf("RecentFile") != -1)
                    addRecentFile(p.getProperty(s));
            }
        } catch (FileNotFoundException ex) {
            LOGGER.debug("Could not read RecentFileList. Did not find file {}", filename);
        } catch (IOException ioe) {
            LOGGER.debug("Could not read RecentFileList. Some IO Error occured ", ioe);
        } finally {
            try {
                if (propStream != null) {
                    propStream.close();
                }
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }
    }

    public String getMostRecent() {
        return mostRecentFile.getAbsolutePath();
    }

    /**
     * write the recent file names to the given properties file. the file will be read (if it
     * exists) and then re-written so no information will be lost.
     */
    public void store(String filename) {
        File localRecentFiles = new File(filename);

        Properties p = new Properties();
        try (FileInputStream fin = new FileInputStream(localRecentFiles);
                FileOutputStream fout = new FileOutputStream(localRecentFiles)) {
            // creates a new file if it does not exist yet
            localRecentFiles.createNewFile();
            p.load(fin);
            store(p);
            p.store(fout, "recent files");
        } catch (IOException ex) {
            LOGGER.info("Cound not write recentFileList", ex);
        }
    }


    private static class RecentFileEntry {

        private String name;
        private int nameStart;
        private final String absolutePath;
        private final JMenuItem menuItem;

        public RecentFileEntry(String absolutePath) {
            this.menuItem = new JMenuItem();
            this.menuItem.setToolTipText(absolutePath);
            this.absolutePath = absolutePath;
            this.nameStart = absolutePath.length();
            makeNameLonger();
        }

        public String getAbsolutePath() {
            return absolutePath;
        }

        public String getName() {
            return name;
        }

        private int getNextNameStart() {
            return absolutePath.lastIndexOf(File.separatorChar, this.nameStart - 1);
        }

        public boolean makeNameLonger() {
            if (this.nameStart == -1) {
                return false;
            }
            this.nameStart = getNextNameStart();
            this.name =
                (nameStart == -1 ? absolutePath : absolutePath.substring(nameStart + 1));
            menuItem.setText(name);
            return true;
        }

        public JMenuItem getMenuItem() {
            return menuItem;
        }

        @Override
        public String toString() {
            return name;
        }
    }
}
