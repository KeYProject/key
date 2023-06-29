package de.uka.ilkd.key.util;

import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.parsing.HasLocation;

import org.antlr.v4.runtime.IntStream;

/**
 * @author Alexander Weigl
 * @version 1 (09.02.23)
 */
public class RecognitionException extends Exception implements HasLocation {
    public IntStream input;
    public Position position;

    public RecognitionException(IntStream input, Position position) {
        this.input = input;
        this.position = position;
    }

    public Position getPosition() {
        return position;
    }

    @Override
    public @Nonnull Location getLocation() {
        return new Location(MiscTools.getURIFromTokenSource(input.getSourceName()), position);
    }
}
