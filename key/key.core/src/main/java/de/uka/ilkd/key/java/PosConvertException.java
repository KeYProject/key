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

package de.uka.ilkd.key.java;


import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.parsing.HasLocation;
import recoder.java.CompilationUnit;
import recoder.kit.UnitKit;
import recoder.service.UnresolvedReferenceException;

import javax.annotation.Nullable;
import java.net.MalformedURLException;

/**
 * A convert exception enriched with a location within a file/source.
 * <p>
 * The source's name itself is not captured.
 */
public class PosConvertException extends ConvertException implements HasLocation {

    private static final long serialVersionUID = 758453353495075586L;

    /**
     * The line
     */
    private final int line;

    /**
     * The column
     */
    private int column;

    /**
     * Instantiates a new exception with position information.
     *
     * @param message the message, not null
     * @param line    the line to point to
     * @param column  the column to point to
     */
    public PosConvertException(String message, int line, int column) {
        super(message);
        this.line = line;
        this.column = column;
    }

    /**
     * Instantiates a new exception with position information.
     *
     * @param cause  the exception causing this instance.
     * @param line   the line to point to
     * @param column the column to point to
     */
    public PosConvertException(Throwable cause, int line, int column) {
        super(cause);
        this.line = line;
        this.column = column;
    }


    /**
     * Gets the line of the exception location.
     *
     * @return the line
     */
    public int getLine() {
        return line;
    }

    /**
     * Gets the column of the exception location.
     *
     * @return the column
     */
    public int getColumn() {
        return column;
    }

    @Nullable
    @Override
    public Location getLocation() throws MalformedURLException {
        Throwable cause = getCause();
        String file = "";
        if (cause instanceof UnresolvedReferenceException) {
            UnresolvedReferenceException ure = (UnresolvedReferenceException) cause;
            CompilationUnit cu = UnitKit.getCompilationUnit(ure.getUnresolvedReference());
            String dataloc = cu.getDataLocation().toString();
            file = dataloc.substring(dataloc.indexOf(':') + 1);
        }
        return new Location(file, getLine(), getColumn());
    }
}