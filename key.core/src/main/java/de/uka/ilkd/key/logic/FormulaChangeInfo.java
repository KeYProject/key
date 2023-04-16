package de.uka.ilkd.key.logic;

/**
 * This class is used to hold information about modified formulas.
 *
 * @see SequentChangeInfo
 */
public class FormulaChangeInfo {
    /** position within the original formula */
    private final PosInOccurrence positionOfModification;
    /** modified formula */
    private final SequentFormula newFormula;

    public FormulaChangeInfo(PosInOccurrence positionOfModification, SequentFormula newFormula) {
        this.newFormula = newFormula;
        this.positionOfModification = positionOfModification;
    }

    public SequentFormula getNewFormula() {
        return newFormula;
    }

    public SequentFormula getOriginalFormula() {
        return getPositionOfModification().sequentFormula();
    }

    /**
     * @return position within the original formula
     */
    public PosInOccurrence getPositionOfModification() {
        return positionOfModification;
    }

    public String toString() {
        return "Replaced " + positionOfModification + " with " + newFormula;
    }
}
