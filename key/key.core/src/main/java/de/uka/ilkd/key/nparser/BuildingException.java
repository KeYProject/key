package de.uka.ilkd.key.nparser;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

public class BuildingException extends RuntimeException {
    private final ParserRuleContext nodeOfFailure;

    public BuildingException(ParserRuleContext node) {
        super(getPosition(node));
        nodeOfFailure = node;
    }

    public BuildingException(ParserRuleContext node, String message) {
        super(message + getPosition(node));
        nodeOfFailure = node;
    }

    public BuildingException(Token t, String message, Throwable cause) {
        super(message + getPosition(t), cause);
        nodeOfFailure = null;

    }

    private static String getPosition(ParserRuleContext node) {
        if (node == null) return " pos n/a";
        return getPosition(node.start);
    }

    private static String getPosition(Token t) {
        return String.format(" %s:%d#%d", t.getInputStream().getSourceName(), t.getLine(), t.getCharPositionInLine());
    }

    public BuildingException(ParserRuleContext node, String message, Throwable cause) {
        super(message + getPosition(node), cause);
        nodeOfFailure = node;
    }

    public BuildingException(ParserRuleContext node, Throwable cause) {
        this(node, cause.getMessage(), cause);
    }

    public BuildingException() {
        this((ParserRuleContext) null);
    }

    public BuildingException(String message) {
        this(null, message);
    }

    public BuildingException(String message, Throwable cause) {
        this((ParserRuleContext) null, message, cause);
    }

    public BuildingException(Throwable cause) {
        this((ParserRuleContext) null, cause);
    }

    public ParserRuleContext getNodeOfFailure() {
        return nodeOfFailure;
    }
}
