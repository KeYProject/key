/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

import java.io.IOException;

/**
 * This runtime exception wraps an IOException thrown by the pretty printer's writer.
 */
public class PrettyPrintingException extends RuntimeException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -4300469088231850754L;

    private final IOException ioe;

    public PrettyPrintingException(IOException ioe) {
        this.ioe = ioe;
    }

    public IOException getWrappedException() {
        return ioe;
    }

    public String toString() {
        return ioe.toString();
    }
}
