// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.gui.configuration.PathConfig;
import java.awt.event.ActionListener;
import java.io.*;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Properties;

import javax.swing.JMenu;
import javax.swing.JMenuItem;

import de.uka.ilkd.key.util.Debug;
import java.awt.event.ActionEvent;

/**
 * This class offers a mechanism to manage recent files; it adds the
 * necessary menu items to a menu or even can provide that menu itself.
 * also it offers a way to read the recent files from a java.util.Properties
 * object and can store them again to a Properties object.
 * This class is a result of the fusion of the RecentFileBuffer and RecentFiles
 * classes.
 * It's not a Menu in itself!!!
 * @author Ute Platzer, with a lot of input from Volker Braun.
 */
public class RecentFileMenu {

    /**
     * The maximum number of recent files displayed.
     */
    private static final int MAX_RECENT_FILES = 8;

    /** this is the maximal number of recent files. */
    private int maxNumberOfEntries;


    private JMenu menu;

    /** the actionListener to be notified of mouse-clicks or other actionevents
     * on the menu items */
    private ActionListener lissy;

    /**
     * list of recent files
     */
    private HashMap<JMenuItem, RecentFileEntry> recentFiles;


    private RecentFileEntry mostRecentFile;

    /**
     * Create a new RecentFiles list.
     * @param listener the ActionListener that will be notified of the user
     * clicked on a recent file menu entry. The selected filename can be
     * determined with the ActionEvent's getSource() method, cast the Object
     * into a JMenuItem and call the getLabel() method.
     * @param maxNumberOfEntries  the maximal number of items/entries in the
     * recent file menu.
     * @param p a Properties object containing information about the recent
     * files to be displayed initially.
     * Or <code>null</code> to use no initial information.
     */
    public RecentFileMenu(final KeYMediator mediator) {
        this.menu = new JMenu("Recent Files");

        this.lissy = new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                mediator.getUI().loadProblem(new File(getAbsolutePath((JMenuItem) e.getSource())));
            }
        };
        this.maxNumberOfEntries = MAX_RECENT_FILES;

        this.recentFiles = new LinkedHashMap<JMenuItem, RecentFileEntry>();

        menu.setEnabled(menu.getItemCount() != 0);
        menu.setIcon(IconFactory.recentFiles(16));

        load(PathConfig.getRecentFileStorage());
    }

    /**
     */
    private void removeFromModelAndView(JMenuItem item, int index) {
	recentFiles.remove(item);
	menu.remove(index);
    }

    /**
     * add file name to the menu
     */
    private void addToModelAndView(final String name) {
        // do not add quick save location to recent files
        if (de.uka.ilkd.key.gui.actions.QuickSaveAction.QUICK_SAVE_PATH.endsWith(name)) return;

        final RecentFileEntry entry = new RecentFileEntry(name);
        if (new File(entry.getAbsolutePath()).exists()) {
            JMenuItem item = new JMenuItem(entry.getFileName());
            item.setToolTipText(entry.getAbsolutePath());
            recentFiles.put(item, entry);
            item.addActionListener(lissy);
            menu.insert(item, 0);
            mostRecentFile = entry;
        }
    }

    /**
     *
     */
    public String getAbsolutePath(JMenuItem item) {
	return recentFiles.get(item).getAbsolutePath();
    }

    /**
     * call this method to add a new file to the beginning of the RecentFiles
     * list. If the name is already part of the list, it will be moved to the
     * first position. No more than a specified maximum number of names will
     * be allowed in the list, and additional names will be removed at the end.
     * (set the maximum number with the {@link #setMaxNumberOfEntries(int i)} method).
     * @param name the name of the file.
     */
    public void addRecentFile(final String name) {
        //Add the name to the recentFileList:
        //check whether this name is already there
	Debug.out("recentfilemenu: add file: ", name);
	Debug.out("recentfilemenu: at menu count:", menu.getItemCount());
        int index = -1;
	JMenuItem item = null;
        for (int i = 0; i < menu.getItemCount(); i++) {
            if (menu.getItem(i)==null) {
		continue;
	    }
            Debug.out("", i);
            Debug.out("item is ", menu.getItem(i));
            Debug.out("name is ", menu.getItem(i).getText());
            if (recentFiles.
		 get(menu.getItem(i)).getAbsolutePath().equals(name)) {
                //this name has to be put at the first position
		item = menu.getItem(i);
                index = i;
                break;
            }
        }

        if (index != -1) {
            //move the name to the first position
	    removeFromModelAndView(item, index);
        }
	// if appropriate, remove the last entry.
	if (menu.getItemCount() == maxNumberOfEntries ) {
	    removeFromModelAndView(menu.getItem(menu.getItemCount()-1),
				   menu.getItemCount()-1);
	}
	addToModelAndView(name);
	menu.setEnabled(menu.getItemCount()!=0);
    }

    /**
     * specify the maximal number of recent files in the list.
     * The default is MAX_RECENT_FILES
     */
    public void setMaxNumberOfEntries(int max) {
        if (maxNumberOfEntries > max && menu.getItemCount() > max) {
            for (int i= menu.getItemCount()-1; i>max; i--) {
                menu.remove(i);
            }

        }
        this.maxNumberOfEntries = max;
    }

    /**
     * the menu where the recent files are kept. If the user didn't specify
     * one in the constructor, a new JMenu is created. It can be accessed
     * via this method.
     */
    public JMenu getMenu() {
        return menu;
    }

    /**
     * read the recent file names from the properties object.
     * the property names are expected to be "RecentFile0" "RecentFile1" ...
     */
    public void load(Properties p) {
        int i=maxNumberOfEntries;
        String s  ;
        do {
            s = p.getProperty("RecentFile"+i);
            if (s != null) addRecentFile(s);
            i--;
        } while (i >= 0);
    }

     /**
     * Put the names of the recent Files into the properties object.
     * The property names are "RecentFile0"  "RecentFile1" ...
     * The values are fully qualified path names.
     */
    public void store(Properties p) {
        //if there's nothing to store:
        for (int i = 0; i< menu.getItemCount(); i++) {
            p.setProperty("RecentFile" + i,
                          getAbsolutePath(menu.getItem(i)));
        }
    }

    /** read the recent files from the given properties file */
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
            Debug.out("Could not read RecentFileList. Did not find file ",
		      filename);
        } catch (IOException ioe) {
            Debug.out("Could not read RecentFileList. Some IO Error occured ",
		      ioe);
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

    public RecentFileEntry getMostRecent() {
        return mostRecentFile;
    }

    /**
     * write the recent file names to the given properties file.
     * the file will be read (if it exists) and then re-written so no
     * information will be lost.
     */
    public void store(String filename) {
	File localRecentFiles = new File(filename);
	FileInputStream fin = null;
	FileOutputStream fout = null;
	Properties p = new Properties();
	try {
	    // creates a new file if it does not exist yet
	    localRecentFiles.createNewFile();
	    fin = new FileInputStream(localRecentFiles);
	    fout = new FileOutputStream(localRecentFiles);
	    p.load(fin);
            store(p);
            p.store(fout, "recent files");
	} catch (IOException ex) {
            System.err.println("Cound not write recentFileList due to "+
		      ex.toString()+"::"+localRecentFiles);
        } finally {
            try {
                if (fin != null) fin.close();
            } catch (IOException e) {
                System.out.println("Closing streams failed.");
            }
            try {
                if (fout != null) fout.close();
            } catch (IOException e) {
                System.out.println("Closing streams failed.");
            }
        }
    }


    public static class RecentFileEntry {

	private String fileName;
	private String absolutePath;

	public RecentFileEntry(String absolutePath) {
	    this.absolutePath = absolutePath;
	    int lastIndex = absolutePath.lastIndexOf(File.separatorChar);

	    this.fileName = (lastIndex == -1 ? absolutePath :
		absolutePath.substring(lastIndex+1, absolutePath.length()));
	}

	public String getAbsolutePath() {
	    return absolutePath;
	}

	public String getFileName() {
	    return fileName;
	}

        @Override
	public String toString() {
	    return fileName;
	}

    }
}
