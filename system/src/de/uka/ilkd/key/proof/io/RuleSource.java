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

import java.io.*;

public abstract class RuleSource {

    public abstract File file();

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
}
