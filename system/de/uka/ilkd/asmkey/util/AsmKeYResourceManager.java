// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.util;

import java.io.File;

/** Class for managing the different resources, especially
 * to the files containing the rules (the path to them,
 * etc....)
 *
 * @author Stanislas Nanchen
 */

public class AsmKeYResourceManager {


    private String homePath;
    private String basePath;
    private String rulesPath;
    private String keyHome;

    public String getAsmKeYPath() {
	return homePath;
    }

    public String getAsmKeYRulesPath() {
	return rulesPath;
    }

    public String getAsmKeYBasePath() {
	return basePath;
    }

    public File[] getAsmKeYRulesFiles() {
	String[] names = System.getProperty("asmkey.rules.files").split(":");
	File[] files = new File[names.length];
	for(int i = 0; i<names.length; i++) {
	    files[i] = new File(rulesPath, names[i]);
	}
	return files;
    }

    public File getIntRulesFile() {
	String file = System.getProperty("asmkey.rules.int");
	return new File(rulesPath, file);
    }

    public File getBooleanRulesFile() {
	String file = System.getProperty("asmkey.rules.boolean");
	return new File(rulesPath, file);
    }

    public String getKeyHomePath() {
	return keyHome;
    }


    /** The constructor is private, we use the singleton pattern */
    private AsmKeYResourceManager() {
	homePath = System.getProperty("asmkey.home.path", System.getProperty("user.dir", "."));
	basePath = System.getProperty("asmkey.base.path");
	if (basePath == null) {
	    basePath = homePath + "/base/";
	}
	rulesPath = System.getProperty("asmkey.rules.path");
	if (rulesPath == null) {
            rulesPath = homePath + "/rules/";
        }
	keyHome = System.getProperty("key.home");
	if (keyHome == null) { keyHome=""; }
    }

    private static AsmKeYResourceManager manager;

    public static AsmKeYResourceManager getInstance() {
	if (manager == null) { manager = new AsmKeYResourceManager(); }
	return manager;
    }
}
