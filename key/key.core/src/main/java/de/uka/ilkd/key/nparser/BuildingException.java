package de.uka.ilkd.key.nparser;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.jetbrains.annotations.Nullable;

import static de.uka.ilkd.key.nparser.builder.BuilderHelpers.getPosition;

public class BuildingException extends RuntimeException {
    private int lineNumber = -1, posInLine = -1, startOffset = -1, endOffset = -1;

    public BuildingException(ParserRuleContext node) {
        super("");
        setPosition(node);
    }

    public BuildingException(ParserRuleContext node, String message) {
        super(message + getPosition(node));
        setPosition(node);
    }

    public BuildingException(@Nullable Token t, String message, Throwable cause) {
        super(message + getPosition(t), cause);
        if (t != null) {
            lineNumber = t.getLine();
            posInLine = t.getCharPositionInLine();
            startOffset = t.getStartIndex();
            endOffset = t.getStopIndex();
        }
    }

    public BuildingException(ParserRuleContext node, String message, Throwable cause) {
        super(message + getPosition(node), cause);
        setPosition(node);
    }

    public BuildingException(ParserRuleContext node, Throwable cause) {
        this(node, cause.getMessage(), cause);
    }

    public BuildingException() {
    }

    public BuildingException(String message) {
        super(message);
    }

    public BuildingException(String message, Throwable cause) {
        this((ParserRuleContext) null, message, cause);
    }

    public BuildingException(Throwable cause) {
        this((ParserRuleContext) null, cause);
    }

    private void setPosition(ParserRuleContext node) {
        if (node != null) {
            lineNumber = node.start.getLine();
            posInLine = node.start.getCharPositionInLine();
            startOffset = node.start.getStartIndex();
            endOffset = node.stop.getStopIndex();
        }
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
}
