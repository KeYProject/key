/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.zip.ZipEntry;
import java.util.zip.ZipException;
import java.util.zip.ZipFile;

import de.uka.ilkd.key.proof.io.consistency.FileRepo;



/**
 * Allows to iterate a zip file to return all matching entries as InputStreams.
 *
 * @author MU
 */


public class ZipFileCollection implements FileCollection {
    final Path path;
    ZipFile zipFile;

    public ZipFileCollection(Path path) {
        this.path = path;
    }


    public Walker createWalker(String[] extensions) throws IOException {
        if (zipFile == null) {
            try {
                zipFile = new ZipFile(path.toFile());
            } catch (ZipException ex) {
                throw new IOException("can't open " + path + ": " + ex.getMessage(), ex);
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
            assert extensions.length > 0;
            this.enumeration = zipFile.entries();
            this.extensions = new ArrayList<>();
            for (String extension : extensions) { this.extensions.add(extension.toLowerCase()); }
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

        @Override
        public Path getCurrentLocation() {
            return path.resolve(currentEntry.toString());
        }

        public String getRelativeLocation() {
            return currentEntry.getName().toString();
        }

        public boolean step() {
            currentEntry = null;
            outer: while (enumeration.hasMoreElements()) {
                var entry = enumeration.nextElement();
                var name = entry.getName().toLowerCase();
                for (String extension : extensions) {
                    if (name.endsWith(extension)) {
                        currentEntry = entry;
                        break outer;
                    }
                }
            }
            return currentEntry != null;
        }

        public String getType() {
            return "zip";
        }
    }

    @Override
    public String toString() {
        return "ZipFileCollection[" + path + "]";
    }
}
