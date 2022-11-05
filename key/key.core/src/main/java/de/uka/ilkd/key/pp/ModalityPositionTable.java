package de.uka.ilkd.key.pp;


/**
 * This is a position table for program modality formulae. In addition to the usual tables, it can
 * store a range of character positions for the first statement in the Java block.
 */

public class ModalityPositionTable extends PositionTable {

    public ModalityPositionTable(int rows) {
        super(rows);
    }

    private Range firstStatementRange = null;


    public void setFirstStatementRange(Range r) {
        firstStatementRange = r;
    }


    public Range getFirstStatementRange() {
        return new Range(firstStatementRange);
    }
}
