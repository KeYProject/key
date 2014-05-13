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

package de.uka.ilkd.key.gui.configuration;

import java.io.File;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * <p>
 * Keeps some central paths to files and directories.
 * </p>
 * <p>
 * By default all KeY configurations are stored in a directory named ".key"
 * inside the user's home directory. In Microsoft windows operating systems
 * this is directly the hard disc that contains the KeY code. 
 * But the eclipse integration requires to change the default location.
 * This is possible via {@link #setKeyConfigDir(String)} which should be 
 * called once before something is done with KeY (e.g. before the 
 * {@link MainWindow} is opened).
 * </p>
 */
public class PathConfig {
    /**
     * The default name of the directory that contains KeY settings.
     */
    public static final String KEY_DIRECTORY_NAME = ".key";

    /** directory where to find the KeY configuration files */ 
    private static String keyConfigDir;
    
    /**
     * In which file to store the recent files.
     */
    public static String recentFileStorage;
    
    public static String proofIndependentSettings;

    /**
     * Initializes the instance variables with the default settings.
     */
    static {
        setKeyConfigDir(System.getProperty("user.home") + File.separator + KEY_DIRECTORY_NAME);
    }
    
    /**
     * Returns the path to the directory that contains KeY configuration files.
     * @return The directory.
     */
    public static String getKeyConfigDir() {
        return keyConfigDir;
    }

    /**
     * Sets the path to the directory that contains KeY configuration files.
     * @param keyConfigDir The new directory to use.
     */
    public static void setKeyConfigDir(String keyConfigDir) {
        PathConfig.keyConfigDir = keyConfigDir;
        PathConfig.recentFileStorage = getKeyConfigDir() + File.separator + "recentFiles.props";
        PathConfig.proofIndependentSettings = getKeyConfigDir() + File.separator + "proofIndependentSettings.props";
    }

    /**
     * Returns the path to the file that is used to store recent files.
     * @return The path to the file.
     */
    public static String getRecentFileStorage() {
        return recentFileStorage;
    }

    /**
     * Returns the path to the file that is used to store proof independent settings.
     * @return The path to the file.
     */
    public static String getProofIndependentSettings() {
        return proofIndependentSettings;
    }
}