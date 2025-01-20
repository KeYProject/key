/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;

import org.antlr.v4.runtime.CharStream;

public abstract class RuleSource {

    // key-file containing ldt declarations
    public static final String ldtFile = "ldt.key";

    public abstract File file();

    /**
     * Provides an URL to the location the RuleSource is read from. This is more general than
     * returning a file (works also e.g. in case of jar files where the file would be
     * "jar:file:///...").
     *
     * @return the location of the RuleSource as url
     * @throws IOException on I/O errors
     */
    public abstract URL url() throws IOException;

    public boolean isDirectory() {
        return file().isDirectory();
    }

    public abstract int getNumberOfBytes();

    public abstract String getExternalForm();

    public abstract InputStream getNewStream();

    public final boolean isAvailable() {
        InputStream inputStream = null;
        try {
            inputStream = getNewStream();
        } catch (final RuntimeException exception) {
            return false;
        } finally {
            if (inputStream != null) {
                try {
                    inputStream.close();
                } catch (final IOException exception) {
                    return false;
                }
            }
        }
        return inputStream != null;
    }

    @Override
    public abstract String toString();

    public abstract CharStream getCharStream() throws IOException;
}
