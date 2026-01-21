package de.uka.ilkd.key.parser;

public class WarningException extends antlr.ANTLRException {

    /**
     *
     */
    private static final long serialVersionUID = 3421160418830554998L;
    private String errorStr = "";

    public WarningException(String errorStr) {
        this.errorStr = errorStr;
    }

    public String getMessage() {
        return errorStr;
    }


    public String toString() {
        return errorStr;
    }

}
