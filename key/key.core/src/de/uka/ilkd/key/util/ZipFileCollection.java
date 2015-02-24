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
import java.io.IOException;
import java.io.InputStream;
import java.util.Enumeration;
import java.util.List;
import java.util.ArrayList;
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
 */


public class ZipFileCollection implements FileCollection {
    
    File file;
    ZipFile zipFile;
    
    public ZipFileCollection(File file)  {
        this.file = file;
    }


    public Walker createWalker(String[] extensions) throws IOException {
        if(zipFile == null)
            try {
                zipFile = new ZipFile(file);
            } catch(ZipException ex) {
                IOException iox = new IOException("can't open " + file + ": " + ex.getMessage());
                iox.initCause(ex);
                throw iox;
            }
        return new Walker(extensions);
    }

    public Walker createWalker(String extension) throws IOException {
        return createWalker(new String[] { extension });
    }

    class Walker implements FileCollection.Walker {

        private Enumeration<? extends ZipEntry> enumeration;
        private ZipEntry currentEntry;
        private List<String> extensions;

        public Walker(String[] extensions) {
            this.enumeration = zipFile.entries();
            this.extensions = new ArrayList<String>();
            for(String extension : extensions) {
              this.extensions.add(extension.toLowerCase());
            }
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
                for(String extension : extensions) {
                  if(extension != null && !currentEntry.getName().toLowerCase().endsWith(extension))
                     currentEntry = null;
                  else
                     break;
                }
            }
            return currentEntry != null;
        }
        
        public String getType() {
            return "zip";
        }

        public DataLocation getCurrentDataLocation() {
            // dont use ArchiveDataLocation this keeps the zip open and keeps reference to it!
            return new SpecDataLocation("zip", file.getAbsolutePath() + "!" + currentEntry.getName());
        }
    }
    
    @Override
    public String toString() {
        return "ZipFileCollection["+ file + "]";
    }
}