package de.uka.ilkd.key.util;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Stack;

import recoder.io.DataFileLocation;
import recoder.io.DataLocation;

public class DirectoryFileCollection implements FileCollection {

    File directory;
    
    public DirectoryFileCollection(File directory) {
        this.directory = directory;
    }

    private static void addAllFiles(File dir, String[] extensions,
                                    List<File> files) {
        for (File file : dir.listFiles()) {
            if(file.isDirectory()) {
                addAllFiles(file, extensions, files);
            } else if(extMatch(file.getName(), extensions)) {
                files.add(file);
            }
        }
    }
    
    private static boolean extMatch(String s, String[] extensions) {
        for(String ext : extensions) {
            if(s.toLowerCase().endsWith(ext.toLowerCase()))
                return true;
        }
        return false;
    }
    
    public Walker createWalker(String... extensions) {
        List<File> files = new ArrayList<File>();
        addAllFiles(directory, extensions, files);
        return new Walker(extensions);
    }


    private static class Walker implements FileCollection.Walker {

        private Iterator<File> iterator;
        private File currentFile;

        public Walker(String[] extensions) {
            
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


}
