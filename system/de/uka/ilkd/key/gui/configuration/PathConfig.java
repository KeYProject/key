// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.gui.configuration;

import java.io.File;

/**
 * keeps some central paths to files and directories
 *
 */
public interface PathConfig {

    /** directory where to find the KeY configuration files */ 
    public static final String KEY_CONFIG_DIR = System.getProperty("user.home")
        + File.separator + ".key";
    
    /**
     * In which file to store the recent files.
     */
    public static final String RECENT_FILES_STORAGE = 
        KEY_CONFIG_DIR + File.separator + "recentFiles.props";
}
