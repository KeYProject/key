package de.uka.ilkd.key.util.parsing;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Recognizer;
import org.antlr.v4.runtime.Token;
import javax.annotation.Nullable;

public class BuildingIssue {
    private final String message;
    private final int lineNumber;
    private final int posInLine;
    private final int startOffset;
    private final int endOffset;
    private final @Nullable Throwable cause;
    private final boolean isWarning;

    public BuildingIssue(String message, @Nullable Throwable cause, boolean isWarning,
            int lineNumber, int posInLine, int startOffset, int endOffset) {
        this.message = message;
        this.lineNumber = lineNumber;
        this.posInLine = posInLine;
        this.startOffset = startOffset;
        this.endOffset = endOffset;
        this.cause = cause;
        this.isWarning = isWarning;
    }


    public static BuildingIssue createError(String message, @Nullable ParserRuleContext token,
            @Nullable Throwable cause) {
        return createError(message, token != null ? token.start : null, cause);
    }

    public static BuildingIssue createError(String message, @Nullable Token token,
            @Nullable Throwable cause) {
        if (token != null) {
            int lineNumber = token.getLine();
            int posInLine = token.getCharPositionInLine();
            int startOffset = token.getStartIndex();
            int endOffset = token.getStopIndex();
            return new BuildingIssue(message, cause, false, lineNumber, posInLine, startOffset,
                endOffset);
        }
        return new BuildingIssue(message, cause, false, -1, -1, -1, -1);
    }

    public static BuildingIssue createWarning(String message, @Nullable ParserRuleContext token,
            @Nullable Throwable cause) {
        return createWarning(message, token != null ? token.start : null, cause);
    }

    public static BuildingIssue createWarning(String message, @Nullable Token token,
            @Nullable Throwable cause) {
        if (token != null) {
            int lineNumber = token.getLine();
            int posInLine = token.getCharPositionInLine();
            int startOffset = token.getStartIndex();
            int endOffset = token.getStopIndex();
            return new BuildingIssue(message, cause, true, lineNumber, posInLine, startOffset,
                endOffset);
        }
        return new BuildingIssue(message, cause, true, -1, -1, -1, -1);
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

    public boolean isWarning() {
        return isWarning;
    }

    public String getMessage() {
        return message;
    }
}
