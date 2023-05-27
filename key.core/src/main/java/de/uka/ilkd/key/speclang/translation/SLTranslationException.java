package de.uka.ilkd.key.speclang.translation;

import java.net.MalformedURLException;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;
import de.uka.ilkd.key.util.parsing.HasLocation;

import org.antlr.v4.runtime.ParserRuleContext;

public class SLTranslationException extends ProofInputException implements HasLocation {
    private final String fileName;
    private final Position pos;

    public SLTranslationException(String message, Throwable cause, String fileName, Position pos) {
        super(message, cause);
        if (fileName == null) {
            throw new IllegalArgumentException();
        }
        if (pos == null) {
            throw new IllegalArgumentException();
        }
        this.fileName = fileName;
        this.pos = pos;
    }

    public SLTranslationException(String message, String fileName, Position pos, Throwable cause) {
        this(message, cause, fileName, pos);
    }

    public SLTranslationException(String message, String fileName, Position pos) {
        this(message, null, fileName, pos);
    }

    public SLTranslationException(String message) {
        this(message, null, "no file", Position.UNDEFINED);
    }

    public SLTranslationException(String message, ParserRuleContext expr) {
        this(message, expr.start.getTokenSource().getSourceName(), Position.fromToken(expr.start));
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

    @Nullable
    @Override
    public Location getLocation() throws MalformedURLException {
        return new Location(getFileName(), pos);
    }
}
