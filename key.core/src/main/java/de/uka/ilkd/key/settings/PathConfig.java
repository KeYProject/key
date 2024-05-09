/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import org.key_project.util.java.IOUtil;

import java.io.File;

/**
 * Keeps some central paths to files and directories.
 * <p>
 * By default all KeY configurations are stored in a directory named ".key" inside the user's home
 * directory. In Microsoft windows operating systems this is directly the hard disc that contains
 * the KeY code. But the eclipse integration requires to change the default location.
 */
public final class PathConfig {

    /**
     * The Java system property used to indicate that the settings in the KeY directory should not
     * be consulted at startup.
     */
    public static final String DISREGARD_SETTINGS_PROPERTY = "key.disregardSettings";

    /**
     * The default name of the directory that contains KeY settings.
     */
    public static final String KEY_DIRECTORY_NAME = ".key";

    /**
     * directory where to find the KeY configuration files
     */
    private static String keyConfigDir = IOUtil.getHomeDirectory() + File.separator + KEY_DIRECTORY_NAME;


    /**
     * In which file to store the recent files.
     */
    private static String recentFileStorage = getKeyConfigDir() + File.separator + "recentFiles.json";

    /**
     * In which file to store the proof-independent settings.
     */
    private static String proofIndependentSettings = getKeyConfigDir() + File.separator + "proofIndependentSettings.props";


    /**
     * Directory in which the log files are stored.
     */
    private static File logDirectory = new File(keyConfigDir, "logs");

    private PathConfig() {
    }

    /**
     * Returns the path to the directory that contains KeY configuration files.
     *
     * @return The directory.
     */
    public static String getKeyConfigDir() {
        return keyConfigDir;
    }

    /**
     * Returns the path to the file that is used to store recent files.
     *
     * @return The path to the file.
     */
    public static String getRecentFileStorage() {
        return recentFileStorage;
    }

    /**
     *
     */
    public static File getLogDirectory() {
        return PathConfig.logDirectory;
    }

    /**
     * Returns the path to the file that is used to store proof independent settings.
     *
     * @return The path to the file.
     */
    public static String getProofIndependentSettings() {
        return proofIndependentSettings;
    }

}
