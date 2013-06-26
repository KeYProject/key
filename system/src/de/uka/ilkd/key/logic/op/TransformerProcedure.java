package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Operators with a restricted/special rule set.
 */
public class TransformerProcedure extends AbstractSortedOperator {

    public static final TransformerProcedure WELL_DEFINEDNESS =
            new TransformerProcedure(new Name("Well-Definedness"));

    protected TransformerProcedure(Name name) {
        super(name, Sort.ANY, false);
    }
}