// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.storage;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.regex.Pattern;

import de.uka.ilkd.asmkey.parser.AstParser;
import de.uka.ilkd.asmkey.parser.ast.AstProof;
import de.uka.ilkd.asmkey.parser.ast.AstUnit;
import de.uka.ilkd.asmkey.util.AsmKeYResourceManager;
import de.uka.ilkd.key.parser.ParserException;

/**
 * Instance of this class are managing the storage of units and proofs
 * for a given directory. for normal operations, there is only one
 * instance of the storage manager; however tests classes may
 * create additional ones.
 *
 * @see TestStorage
 * @author Stanislas Nanchen
 */
public class StorageManager {
    
    private File mainDirectory;
    private File baseDirectory;
    
    private static FilenameFilter filter;
    private static FilenameFilter projectFilter;
    private static FilenameFilter proofFilter;
   
    

    public StorageManager(String mainDirectoryPath) throws StorageException {
	mainDirectory = directory(mainDirectoryPath, "main");
	baseDirectory = directory
	    (AsmKeYResourceManager.getInstance().getAsmKeYBasePath(), "base");
    }

    private File directory(String path, String kind) throws StorageException {
	File directory = new File(path);
	if (!directory.isDirectory()) {
	    throw new StorageException("The " + kind + " directory " + path +
				       " does not exists or is not a directory.");
	}
	return directory;
    }


    /**
     * this method retrieve the name of all projects, i.e. the
     * names of the directories in the main directy.
     */
    public String[] getProjectIds() {
	return mainDirectory.list(projectFilter);
    }

    /** for test purposes only */
    String[] getUnitIds(String project) throws StorageException {
	File projectDir = directory
	    (mainDirectory.getAbsolutePath() + File.separator + project,
	     "project");
	return projectDir.list(filter);
    }

    /**
     * this method allows to get the AstUnit trees of the user defined
     * units, stored in the {@link #mainDirectoryPath}.
     */
    public AstUnit[] getUnitAstTrees(String project) throws ParserException, StorageException {
	File projectDir = directory
	    (mainDirectory.getAbsolutePath() + File.separator + project,
	     "project");
	return getAstTrees(projectDir);
    }

    public AstUnit[] getAstTrees(File directory)
	throws ParserException, StorageException {
	File file;
	AstUnit[] units;
	String[] fileNames = directory.list(filter);
	
	units = new AstUnit[fileNames.length];
	for(int i = 0; i<fileNames.length; i++) {
	    try {
		units[i] = AstParser.parseUnit(new File(directory, fileNames[i]));
		// we check the name of the unit and of the file are corresponding
		if (!fileNames[i].equals(units[i].getUnitId().getText() + ".unit")) {
		    throw new ParserException("The name of the unit " +
					      units[i].getUnitId().getText() +
					      " and the name of the file " + fileNames[i] +
					      " do not correspond.", units[i].getLocation());
		}
	    } catch (FileNotFoundException e) {
		throw new StorageException(e);
	    }
	}
	return units;
    }

    /**
     * this method allows to get the AstUnit trees of the base units of the
     * standart library. they are stored at a standart location given
     * by a java property at startup.
     */
    public AstUnit[] getBaseUnitAstTrees() throws ParserException, StorageException {
	return getAstTrees(baseDirectory);
    }

    /* --- proof stuff --- */

    private File getProofDirectory(String project, String unit)
	throws StorageException {
	return directory
	    (mainDirectory.getAbsolutePath() + File.separator + project + File.separator +
	     "proofs" + File.separator + unit,
	     "proof");
    }

    public File getProofFileForSaving(String project, String unit, String prop)
	throws StorageException {
	File directory = getProofDirectory(project, unit);
	File proof = new File(directory, prop + ".proof");
	try {
	    proof.createNewFile();
	} catch (SecurityException e) {
	    throw new StorageException(e);
	} catch (IOException e) {
	    throw new StorageException(e);
	}
	return proof;
    }

    private AstProof getAstProof(File directory, String unit, String prop)
	throws ParserException, StorageException {
	try {
	    AstProof proof = AstParser.parseProof(new File(directory, prop + ".proof"));
	    // we must check the name of the proof problem and the file are corresponding
	    if (!proof.getProofId().getText().equals(unit + "." + prop)) {
		throw new ParserException("The name of the proof " +
					  proof.getProofId().getText() +
					  " and the name of the file " + prop +
					  " do not correspond.", proof.getLocation());
	    }
	    return proof;
	} catch (FileNotFoundException e) {
	    throw new StorageException(e);
	}
    }
    
    String[] getAstProofIds(String project, String unit)
	throws StorageException {
	File directory = getProofDirectory(project, unit);
	return directory.list(proofFilter);
    }
    
    public AstProof getAstProof(String project, String unit, String prop) 
	throws ParserException, StorageException {
	return getAstProof(getProofDirectory(project, unit), unit,
			   prop);
    }

    /* --- static initialisation --- */

    static {
	filter = new FilenameFilter() {
		private Pattern p = Pattern.compile(".*\\.unit$");
		
		public boolean accept(File dir, String name) {
		    return p.matcher(name).matches();
		}
	    };

	projectFilter = new FilenameFilter() {
		public boolean accept(File dir, String name) {
		    try {
			return (new File(dir, name)).isDirectory();
		    } catch (SecurityException e) {
			return false;
		    }
		}
	    };

	proofFilter = new FilenameFilter() {
		private Pattern p = Pattern.compile(".*\\.proof$");
		
		public boolean accept(File dir, String name) {
		    return p.matcher(name).matches();
		}
	    };
    }

}
