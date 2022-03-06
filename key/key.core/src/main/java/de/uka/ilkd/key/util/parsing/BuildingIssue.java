package de.uka.ilkd.key.util.parsing;

import de.uka.ilkd.key.parser.Location;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

import javax.annotation.Nullable;
import java.net.MalformedURLException;
import java.net.URI;
import java.net.URISyntaxException;

public class BuildingIssue implements HasLocation {
    private final String message;
    private final int lineNumber;
    private final int posInLine;
    private final int startOffset;
    private final int endOffset;

    @Nullable
    private final Throwable cause;
    @Nullable
    private final boolean isWarning;

    private final URI location;

    public BuildingIssue(String message, @Nullable Throwable cause,
                         boolean isWarning,
                         int lineNumber, int posInLine, int startOffset, int endOffset, URI location) {
        this.message = message;
        this.lineNumber = lineNumber;
        this.posInLine = posInLine;
        this.startOffset = startOffset;
        this.endOffset = endOffset;
        this.cause = cause;
        this.isWarning = isWarning;
        this.location = location;
    }


    public static BuildingIssue createError(String message,
                                            @Nullable ParserRuleContext token, @Nullable Throwable cause) {
        return createError(message, token != null ? token.start : null, cause);
    }

    public static BuildingIssue createError(String message, @Nullable Token token, @Nullable Throwable cause) {
        if (token != null) {
            int lineNumber = token.getLine();
            int posInLine = token.getCharPositionInLine();
            int startOffset = token.getStartIndex();
            int endOffset = token.getStopIndex();
            var location = toUri(token.getTokenSource().getSourceName());
            return new BuildingIssue(message, cause, false, lineNumber, posInLine, startOffset, endOffset, location);
        }
        return new BuildingIssue(message, cause, false, -1, -1, -1, -1, null);
    }

    private static URI toUri(String sourceName) {
        try {
            return new URI(sourceName);
        } catch (URISyntaxException e) {
            e.printStackTrace();
        }
        return null;
    }

    public static BuildingIssue createWarning(String message,
                                              @Nullable ParserRuleContext token, @Nullable Throwable cause) {
        return createWarning(message, token != null ? token.start : null, cause);
    }

    public static BuildingIssue createWarning(String message, @Nullable Token token, @Nullable Throwable cause) {
        if (token != null) {
            int lineNumber = token.getLine();
            int posInLine = token.getCharPositionInLine();
            int startOffset = token.getStartIndex();
            int endOffset = token.getStopIndex();
            var location = toUri(token.getTokenSource().getSourceName());
            return new BuildingIssue(message, cause, true, lineNumber, posInLine, startOffset, endOffset, location);
        }
        return new BuildingIssue(message, cause, true, -1, -1, -1, -1, null);
    }


    public int getLineNumber() {
        return lineNumber;
    }

    public int getPosInLine() {
        return posInLine;
    }

    public int getStartOffset() {
        return startOffset;
    }

    public int getEndOffset() {
        return endOffset;
    }

    @Nullable
    @Override
    public Location getLocation() throws MalformedURLException {
        return new Location(location.toURL(), lineNumber, posInLine);
    }
}
