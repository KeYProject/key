package de.uka.ilkd.key.util;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.Enumeration;
import java.util.NoSuchElementException;
import java.util.zip.ZipEntry;
import java.util.zip.ZipException;
import java.util.zip.ZipFile;
import java.util.zip.ZipInputStream;

import recoder.io.ArchiveDataLocation;
import recoder.io.DataLocation;


/**
 * Allows to iterate a zip file to return all matching entries
 * as InpuStreams.
 * 
 * @author MU
 *
 */


public class ZipFileCollection implements FileCollection {
    
    URL url;
    
    public ZipFileCollection(File file) {
        this(mkURL(file));
    }

    public ZipFileCollection(URL url) {
        this.url = url;
    }

    public Walker createWalker(String... extensions) throws IOException {
        return new Walker(extensions);
    }
    
    private static URL mkURL(File f) {
        try {
            return f.toURL();
        } catch (MalformedURLException e) {
            // this may never happen!
            throw new Error(e);
        }
    }

    class Walker implements FileCollection.Walker {

        private ZipEntry currentEntry;
        private String[] extensions;
        private ZipInputStream zis;

        public Walker(String[] extensions) throws IOException {
            zis = new ZipInputStream(url.openStream()); 
            this.extensions = extensions;
        }

        public String getCurrentName() {
            if(currentEntry == null)
                throw new NoSuchElementException();
            else
                return currentEntry.getName();
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
                if(extMatch(currentEntry.getName()))
                    currentEntry = null;
            }
            return currentEntry != null;
        }
        
        private boolean extMatch(String s) {
            for(String ext : extensions) {
                if(s.toLowerCase().endsWith(ext.toLowerCase()))
                    return true;
            }
            return false;
        }

        public String getType() {
            return "zip";
        }

        public DataLocation getCurrentDataLocation() {
            // dont use ArchiveDataLocation this opens the zip and keeps reference to it!
            return new SpecDataLocation("zip", url.toString() + "!" + getCurrentName());
        }

        
    }
}
