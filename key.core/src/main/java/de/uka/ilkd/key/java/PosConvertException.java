/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;


import java.net.MalformedURLException;
import javax.annotation.Nullable;

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.parsing.HasLocation;

import recoder.java.CompilationUnit;
import recoder.kit.UnitKit;
import recoder.service.UnresolvedReferenceException;

/**
 * A convert exception enriched with a location within a file/source.
 * <p>
 * The source's name itself is not captured.
 */
public class PosConvertException extends ConvertException implements HasLocation {

    private static final long serialVersionUID = 758453353495075586L;

    /**
     * The file this error references. May be null.
     */
    private String file;

    /**
     * The position
     */
    private final Position position;

    /**
     * Instantiates a new exception with position information.
     *
     * @param message the message, not null
     * @param position the position
     */
    public PosConvertException(String message, Position position) {
        super(message);
        this.position = position;
        this.file = null;
    }

    /**
     * Instantiates a new exception with position and file information.
     *
     * @param message the message, not null
     * @param position the position
     * @param file the file that contains the error
     */
    public PosConvertException(String message, Position position, String file) {
        super(message);
        this.position = position;
        this.file = file;
    }

    /**
     * Gets the position of the exception location.
     *
     * @return the position
     */
    public Position getPosition() {
        return position;
    }

    @Nullable
    @Override
    public Location getLocation() throws MalformedURLException {
        Throwable cause = getCause();
        if (this.file == null) {
            if (cause instanceof UnresolvedReferenceException) {
                UnresolvedReferenceException ure = (UnresolvedReferenceException) cause;
                CompilationUnit cu = UnitKit.getCompilationUnit(ure.getUnresolvedReference());
                String dataloc = cu.getDataLocation().toString();
                this.file = dataloc.substring(dataloc.indexOf(':') + 1);
            }
        }
        return Location.fromFileName(file, position);
    }
}
