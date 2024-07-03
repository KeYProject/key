package de.uka.ilkd.key.settings;

import java.io.File;

import org.key_project.util.java.IOUtil;

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
     * The Java system property used to indicate that the
     * settings in the KeY directory should not be consulted
     * at startup.
     */
    public static final String DISREGARD_SETTINGS_PROPERTY =
            "key.disregardSettings";

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
        setKeyConfigDir(IOUtil.getHomeDirectory() + File.separator + KEY_DIRECTORY_NAME);
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