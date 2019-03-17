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

package de.uka.ilkd.key.util;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

import recoder.io.DataFileLocation;
import recoder.io.DataLocation;

/**
 * This class is used to describe a directory structure as a repository for
 * files to read in. A directory is read recursively.
 * 
 * All files are enumerated when the walker is created. Any file added
 * afterwards will not looked at when iterating.
 * 
 * For more info see {@link FileCollection}
 * 
 * @author MU
 */
public class DirectoryFileCollection implements FileCollection {

    /** directory under inspection */
    private File directory;
    
    /**
     * create a new File collection for a given directory
     * The argument may be a single file also. A directory is read recursively.
     * 
     * @param directory directory to iterate through, 
     */
    public DirectoryFileCollection(File directory) {
        this.directory = directory;
    }

    /*
     * add all files in or under dir to a file list. Extension is tested
     */
    private static void addAllFiles(File dir, String extension,
                                    List<File> files) {
        File[] listFiles = dir.listFiles();
        
        if(listFiles == null)
            throw new IllegalArgumentException(dir+" is not a directory or cannot be read!");
        
        for (File file : listFiles) {
            if(file.isDirectory()) {
                addAllFiles(file, extension, files);
            } else if(extension == null || file.getName().toLowerCase().endsWith(extension)) {
                files.add(file);
            }
        }
    }
    
    /**This method is to fix the bug: "0965: Creating arrays of primitive type fails when using \bootclasspath "
     * The method sorts the List of File that is given as parameter according to the following criteria:
     * - File paths that contain the subpath "java/lang" are stored before other file paths.
     * - If there is a File that contains the subpath "java/lang/Object.java" then it is stored at the very beginning of the list. 
     * @author gladisch */ 
    private static void sortFiles(List<File> files){
        for(int a=0;a<files.size()-1;a++){
            for(int b= a+1;b<files.size();b++){
        	if(!(a<b))throw new RuntimeException("Incorrect sorting algorithms.");
        	File fa=files.get(a);
        	File fb=files.get(b);
        	
        	//Check if the path A contains the substring "JAVA/LANG"
        	String pathA = fa.getPath().toUpperCase().replace('\\', '/');
        	boolean A_isObjectClass = pathA.indexOf("JAVA/LANG/OBJECT.JAVA")!=-1;
        	
        	//Check if the path B contains the substring "JAVA/LANG/OBJECT.JAVA"
        	String pathB = fb.getPath().toUpperCase().replace('\\', '/');
        	boolean B_inJavaLang = pathB.indexOf("JAVA/LANG")!=-1;
        	
        	//Switch files to ensure the desired order of files
        	if(B_inJavaLang && !A_isObjectClass){
        	    files.set(a, fb);
        	    files.set(b, fa);
        	}
            }
        }
    }
    
    
    /*
     * enumerate all files in a list and store that list in the walker.
     * 
     * @see de.uka.ilkd.key.util.FileCollection#createWalker(java.lang.String)
     */
    public Walker createWalker(String extension) {
        List<File> files = new ArrayList<File>();
        addAllFiles(directory, extension, files);
        sortFiles(files);
        return new Walker(files.iterator());
    }


    /*
     * enumerate all files in a list and store that list in the walker.
     * 
     * @see de.uka.ilkd.key.util.FileCollection#createWalker(java.lang.String[])
     */
    public Walker createWalker(String[] extensions) {
        List<File> files = new ArrayList<File>();
        for(String extension : extensions) {
    	    addAllFiles(directory, extension, files);
        }
        sortFiles(files);
        return new Walker(files.iterator());
    }

    /*
     * This class keeps an internal list of files to be iterated that is created at
     * construction time.
     */
    private static class Walker implements FileCollection.Walker {

        private Iterator<File> iterator;
        private File currentFile;

        public Walker(Iterator<File> iterator) {
            this.iterator = iterator;
        }

        public String getCurrentName() {
            if(currentFile == null)
                throw new NoSuchElementException();
            else
                return currentFile.getPath();
        }

        public InputStream openCurrent() throws IOException {
            if(currentFile == null)
                throw new NoSuchElementException();
            else
                return new FileInputStream(currentFile);

        }

        public boolean step() {
            try {
                currentFile = iterator.next();
                return true;
            } catch(NoSuchElementException ex) {
                currentFile = null;
                return false;
            }
        }

        public String getType() {
            return "file";
        }

        public DataLocation getCurrentDataLocation() {
            return new DataFileLocation(currentFile);
        }
    }

    @Override
    public String toString() {
        return "DirectoryFileCollection[" + directory + "]";
    }

}