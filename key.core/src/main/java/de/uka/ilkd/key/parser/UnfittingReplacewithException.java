/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.parser;

import org.antlr.runtime.RecognitionException;

public class UnfittingReplacewithException
        extends RecognitionException {

    /**
     *
     */
    private static final long serialVersionUID = -497885048593588941L;
    private String description;
    private String filename;

    public UnfittingReplacewithException(String description,
            String filename,
            int line, int column) {
        super();
        this.filename = filename;
        this.line = line;
        this.charPositionInLine = column;
        this.description = description;
    }


    public String getMessage() {
        return (filename != null ? filename + ":" : "") + description;
    }

}
