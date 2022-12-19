package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;
import de.uka.ilkd.key.util.parsing.HasLocation;
import org.antlr.v4.runtime.ParserRuleContext;

import javax.annotation.Nullable;
import java.net.MalformedURLException;

public class SLTranslationException extends ProofInputException implements HasLocation {
    private final String fileName;
    private final Position pos;

    public SLTranslationException(String message, Throwable cause, String fileName, Position pos) {
        super(message, cause);
        if (fileName == null)
            throw new IllegalArgumentException();
        if (pos == null)
            throw new IllegalArgumentException();
        this.fileName = fileName;
        this.pos = pos;
    }

    public SLTranslationException(String message, String fileName, Position pos, Throwable cause) {
        this(message, cause, fileName, pos);
    }

    public SLTranslationException(String message, String fileName, Position pos) {
        this(message, null, fileName, pos);
    }

    public SLTranslationException(String message, String fileName, int line, int column) {
        this(message, null, fileName, new Position(line, column));
    }

    public SLTranslationException(String message) {
        this(message, null, "no file", Position.UNDEFINED);
    }

    public SLTranslationException(String message, Throwable cause) {
        this(message);
    }

    public SLTranslationException(String message, ParserRuleContext expr) {
        this(message, expr.start.getTokenSource().getSourceName(),
            new Position(expr.start.getLine(), expr.start.getCharPositionInLine()));
    }

    public SLTranslationException(String message, LabeledParserRuleContext expr) {
        this(message, expr.first);
    }

    public String getFileName() {
        return fileName;
    }

    public Position getPosition() {
        return pos;
    }

    public int getLine() {
        return pos.getLine();
    }

    public int getColumn() {
        return pos.getColumn();
    }

    @Nullable
    @Override
    public Location getLocation() throws MalformedURLException {
        return new Location(getFileName(), getLine(), getColumn());
    }
}
