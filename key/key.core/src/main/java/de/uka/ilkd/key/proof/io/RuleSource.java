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
package de.uka.ilkd.key.proof.io;

import org.antlr.v4.runtime.CharStream;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;

public abstract class RuleSource {

    // key-file containing ldt declarations
    public static final String ldtFile = "ldt.key";

    public abstract File file();

    /**
     * Provides an URL to the location the RuleSource is read from.
     * This is more general than returning a file (works also e.g. in case of jar files where the
     * file would be "jar:file:///...").
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
