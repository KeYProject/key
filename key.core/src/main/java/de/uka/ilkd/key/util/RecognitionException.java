package de.uka.ilkd.key.util;

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.parsing.HasLocation;
import org.antlr.v4.runtime.IntStream;

import javax.annotation.Nullable;
import java.net.MalformedURLException;

/**
 * @author Alexander Weigl
 * @version 1 (09.02.23)
 */
public class RecognitionException extends Exception implements HasLocation {
    public IntStream input;
    public int line;
    public int charPositionInLine;

    public RecognitionException(IntStream input, int line, int charInLine) {
        this.input = input;
        this.line = line;
        this.charPositionInLine = charInLine;
    }

    @Nullable
    @Override
    public Location getLocation() throws MalformedURLException {
        return new Location(input.getSourceName(), line, charPositionInLine + 1);
    }
}
