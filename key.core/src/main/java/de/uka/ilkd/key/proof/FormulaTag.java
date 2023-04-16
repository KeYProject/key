package de.uka.ilkd.key.proof;

/**
 * Class whose instances represent tags to identify the formulas of sequents persistently, i.e. a
 * tag does not become invalid when a formula is modified by a rule application. Tags are managed by
 * the class FormulaTagManager for each Node
 */
public final class FormulaTag {

    static int counter = 0;
    final int i;

    FormulaTag() {
        i = counter++;
    }

    public String toString() {
        return String.valueOf(i);
    }

}
