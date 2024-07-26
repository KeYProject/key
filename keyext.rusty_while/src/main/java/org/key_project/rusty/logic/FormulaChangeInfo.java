package org.key_project.rusty.logic;

public record FormulaChangeInfo(PosInOccurrence positionOfModification, SequentFormula newFormula) {

    public SequentFormula getOriginalFormula() {
        return positionOfModification().sequentFormula();
    }

    /**
     * @return position within the original formula
     */
    @Override
    public PosInOccurrence positionOfModification() {
        return positionOfModification;
    }

    public String toString() {
        return "Replaced " + positionOfModification + " with " + newFormula;
    }

}
