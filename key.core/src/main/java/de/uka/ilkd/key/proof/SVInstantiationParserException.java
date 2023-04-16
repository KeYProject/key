package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.java.Position;

public class SVInstantiationParserException extends SVInstantiationExceptionWithPosition {

    /**
     *
     */
    private static final long serialVersionUID = 4411508672178909020L;
    private final String instantiation;
    private final String detail;

    public SVInstantiationParserException(String instantiation, Position position, String detail,
            boolean inIfSequent) {
        super("Parser Error", position, inIfSequent);
        this.instantiation = instantiation;
        this.detail = (detail == null) ? "" : detail;
    }

    private String space(int i) {
        StringBuilder res = new StringBuilder();
        for (int j = 0; j < i; j++) {
            res.append(" ");
        }
        return res.toString();
    }

    public String getMessage() {
        int column = getPosition().column();

        String msg = super.getMessage();
        // needs non-prop font: msg +="\n"+inst;
        if (column > 0) {
            // needs non-prop font: msg +="\n"+space(column-1)+"^";
            String[] rows = instantiation.split("\n");
            StringBuilder sb = new StringBuilder(rows[getPosition().line() - 1]);
            sb.insert(column - 1, " ~~> ");
            msg += "\noccurred at: " + sb;
        } else {
            msg += "\noccurred in:" + instantiation;
        }

        msg += "\nDetail:\n" + detail;

        return msg;
    }

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
        return getMessage();
    }

    @Override
    public SVInstantiationParserException initCause(Throwable cause) {
        super.initCause(cause);
        return this;
    }
}
