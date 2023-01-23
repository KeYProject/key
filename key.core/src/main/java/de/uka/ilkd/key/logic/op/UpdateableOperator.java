package de.uka.ilkd.key.logic.op;


/**
 * Operators implementing this interface may stand for locations as well. This means e.g. occur as
 * top level operators on the left side of an assignment pair of an update.
 */
public interface UpdateableOperator extends SortedOperator, ParsableVariable {

}
