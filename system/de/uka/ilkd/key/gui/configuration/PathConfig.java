package de.uka.ilkd.key.gui.configuration;

import java.io.File;

/**
 * keeps some central paths to files and directories
 *
 */
public interface PathConfig {

    /** directory where to find the KeY configuration files */ 
    public static final String KEY_CONFIG_DIR = System.getProperty("user.home")
        + File.separator + ".key-1.2";
    /**
     * In which file to store the recent files.
     */
    public static final String RECENT_FILES_STORAGE = 
        KEY_CONFIG_DIR + File.separator + "recentFiles.props";

}
