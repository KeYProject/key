// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.util;

import java.io.*;
import java.util.*;

import recoder.io.*;

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
    
    /*
     * enumerate all files in a list and store that list in the walker.
     * 
     * @see de.uka.ilkd.key.util.FileCollection#createWalker(java.lang.String)
     */
    public Walker createWalker(String extension) {
        List<File> files = new ArrayList<File>();
        addAllFiles(directory, extension, files);
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
