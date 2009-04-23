// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.parser;


/** 
 * This class represents a location in a file.  It consists of a
 * filename, a line number and a column number. The filename may be
 * null, if the file is unknown (e.g. standard input). The class is
 * mainly used for parser exceptions.
 *
 * @author Hubert Schmid
 */

public final class Location {

    /* --- constructors --- */

    /** @param filename the filename may be null. */
    public Location(String filename, int line, int column) {
        this.filename = filename;
        this.line = line;
        this.column = column;
    }


    /* --- methods --- */

    /** @return the filename may be null */
    public String getFilename() {
        return filename;
    }

    public int getLine() {
        return line;
    }

    public int getColumn() {
        return column;
    }

    /** Internal string representation. Do not rely on format! */
    public String toString() {
        return "[" + filename + ":" + line + "," + column + "]";
    }


    /* --- fields --- */

    private final String filename;

    private final int line;

    private final int column;

}
