package de.uka.ilkd.key.util;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.Enumeration;
import java.util.NoSuchElementException;
import java.util.zip.ZipEntry;
import java.util.zip.ZipException;
import java.util.zip.ZipFile;

import recoder.io.DataLocation;


/**
 * Allows to iterate a zip file to return all matching entries
 * as InpuStreams.
 * 
 * @author MU
 *
 */


public class ZipFileCollection implements FileCollection {
    
    File file;
    ZipFile zipFile;
    
    public ZipFileCollection(File file)  {
        this.file = file;
    }

    public Walker createWalker(String extension) throws ZipException, IOException {
        if(zipFile == null)
            zipFile = new ZipFile(file);
        return new Walker(extension.toLowerCase());
    }
    

    class Walker implements FileCollection.Walker {

        private Enumeration<? extends ZipEntry> enumeration;
        private ZipEntry currentEntry;
        private String extension;

        public Walker(String extension) {
            this.enumeration = zipFile.entries();
            this.extension = extension;
        }

        public String getCurrentName() {
            if(currentEntry == null)
                throw new NoSuchElementException();
            else
                return file.getAbsolutePath() + File.separatorChar +  currentEntry.getName();
        }

        public InputStream openCurrent() throws IOException {
            if(currentEntry == null)
                throw new NoSuchElementException();
            else
                return zipFile.getInputStream(currentEntry);
        }

        public boolean step() {
            currentEntry = null;
            while(enumeration.hasMoreElements() && currentEntry == null) {
                currentEntry = enumeration.nextElement();
                if(currentEntry.getName().toLowerCase().endsWith(extension))
                    currentEntry = null;
            }
            return currentEntry != null;
        }
        
        public String getType() {
            return "zip";
        }

        public DataLocation getCurrentDataLocation() {
            // dont use ArchiveDataLocation this opens the zip and keeps reference to it!
            return new SpecDataLocation("zip", file.getAbsolutePath() + "!" + currentEntry.getName());
        }
    }
}