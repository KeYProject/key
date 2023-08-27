/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.zip.ZipEntry;
import java.util.zip.ZipException;
import java.util.zip.ZipFile;

import de.uka.ilkd.key.java.recoderext.URLDataLocation;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import recoder.io.DataLocation;


/**
 * Allows to iterate a zip file to return all matching entries as InpuStreams.
 *
 * @author MU
 */


public class ZipFileCollection implements FileCollection {
    private static final Logger LOGGER = LoggerFactory.getLogger(ZipFileCollection.class);

    final File file;
    ZipFile zipFile;

    public ZipFileCollection(File file) {
        this.file = file;
    }


    public Walker createWalker(String[] extensions) throws IOException {
        if (zipFile == null) {
            try {
                zipFile = new ZipFile(file);
            } catch (ZipException ex) {
                IOException iox =
                    new IOException("can't open " + file + ": " + ex.getMessage(), ex);
                throw iox;
            }
        }
        return new Walker(extensions);
    }

    public Walker createWalker(String extension) throws IOException {
        return createWalker(new String[] { extension });
    }

    class Walker implements FileCollection.Walker {

        private final Enumeration<? extends ZipEntry> enumeration;
        private ZipEntry currentEntry;
        private final List<String> extensions;

        public Walker(String[] extensions) {
            this.enumeration = zipFile.entries();
            this.extensions = new ArrayList<>();
            for (String extension : extensions) {
                this.extensions.add(extension.toLowerCase());
            }
        }

        public String getCurrentName() {
            if (currentEntry == null) {
                throw new NoSuchElementException();
            } else {
                return file.getAbsolutePath() + File.separatorChar + currentEntry.getName();
            }
        }

        public InputStream openCurrent() throws IOException {
            if (currentEntry == null) {
                throw new NoSuchElementException();
            } else {
                return zipFile.getInputStream(currentEntry);
            }
        }

        @Override
        public InputStream openCurrent(FileRepo fileRepo) throws IOException {
            if (currentEntry == null) {
                throw new NoSuchElementException();
            } else if (fileRepo != null) {
                // request an InputStream from the FileRepo
                URI uri = MiscTools.getZipEntryURI(zipFile, currentEntry.getName());
                return fileRepo.getInputStream(uri.toURL());
            } else {
                return openCurrent(); // fallback without FileRepo
            }
        }

        public boolean step() {
            currentEntry = null;
            while (enumeration.hasMoreElements() && currentEntry == null) {
                currentEntry = enumeration.nextElement();
                for (String extension : extensions) {
                    if (extension != null
                            && !currentEntry.getName().toLowerCase().endsWith(extension)) {
                        currentEntry = null;
                    } else {
                        break;
                    }
                }
            }
            return currentEntry != null;
        }

        public String getType() {
            return "zip";
        }

        public DataLocation getCurrentDataLocation() {
            // dont use ArchiveDataLocation this keeps the zip open and keeps reference to it!
            try {
                // since we actually return a zip/jar, we use URLDataLocation
                URI uri = MiscTools.getZipEntryURI(zipFile, currentEntry.getName());
                return new URLDataLocation(uri.toURL());
            } catch (IOException e) {
                LOGGER.warn("Failed to get zip entry uri", e);
            }
            return SpecDataLocation.UNKNOWN_LOCATION; // fallback
        }
    }

    @Override
    public String toString() {
        return "ZipFileCollection[" + file + "]";
    }
}
