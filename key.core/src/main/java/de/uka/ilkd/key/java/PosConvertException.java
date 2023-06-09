package de.uka.ilkd.key.java;


import java.net.MalformedURLException;
import java.net.URI;
import javax.annotation.Nullable;

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.parsing.HasLocation;

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
    private URI file;

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
    public PosConvertException(String message, Position position, URI file) {
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
        return new Location(file, position);
    }
}
