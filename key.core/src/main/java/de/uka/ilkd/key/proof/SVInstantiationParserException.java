package de.uka.ilkd.key.proof;

public class SVInstantiationParserException extends SVInstantiationExceptionWithPosition {

    /**
     *
     */
    private static final long serialVersionUID = 4411508672178909020L;
    private String instantiation;
    private String detail;

    public SVInstantiationParserException(String instantiation, int row, int column, String detail,
            boolean inIfSequent) {
        super("Parser Error", row, column, inIfSequent);
        this.instantiation = instantiation;
        this.detail = (detail == null) ? "" : detail;
    }

    private String space(int i) {
        StringBuffer res = new StringBuffer();
        for (int j = 0; j < i; j++) {
            res.append(" ");
        }
        return res.toString();
    }

    public String getMessage() {

        int column = getColumn();

        String errmsg = super.getMessage();
        // needs non-prop font: errmsg +="\n"+inst;
        if (column > 0) {
            // needs non-prop font: errmsg +="\n"+space(column-1)+"^";
            String[] rows = instantiation.split("\n");
            StringBuffer sb = new StringBuffer(rows[getRow() - 1]);
            sb.insert(column - 1, " ~~> ");
            errmsg += "\noccurred at: " + sb.toString();
        } else {
            errmsg += "\noccurred in:" + instantiation;
        }

        errmsg += "\nDetail:\n" + detail;

        return errmsg;
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
