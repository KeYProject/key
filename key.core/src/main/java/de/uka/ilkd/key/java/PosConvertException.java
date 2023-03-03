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
     * The file this error references. May be null.
     */
    private String file;

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
     * @param line the line to point to
     * @param column the column to point to
     */
    public PosConvertException(String message, int line, int column) {
        super(message);
        this.line = line;
        this.column = column;
        this.file = null;
    }

    /**
     * Instantiates a new exception with position and file information.
     *
     * @param message the message, not null
     * @param line the line to point to
     * @param column the column to point to
     * @param file the file that contains the error
     */
    public PosConvertException(String message, int line, int column, String file) {
        super(message);
        this.line = line;
        this.column = column;
        this.file = file;
    }

    /**
     * Instantiates a new exception with position information.
     *
     * @param cause the exception causing this instance.
     * @param line the line to point to
     * @param column the column to point to
     */
    public PosConvertException(Throwable cause, int line, int column) {
        super(cause);
        this.line = line;
        this.column = column;
        this.file = null;
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
        if (this.file == null) {
            if (cause instanceof UnresolvedReferenceException) {
                UnresolvedReferenceException ure = (UnresolvedReferenceException) cause;
                CompilationUnit cu = UnitKit.getCompilationUnit(ure.getUnresolvedReference());
                String dataloc = cu.getDataLocation().toString();
                this.file = dataloc.substring(dataloc.indexOf(':') + 1);
            } else {
                this.file = "";
            }
        }
        return new Location(file, getLine(), getColumn());
    }
}
