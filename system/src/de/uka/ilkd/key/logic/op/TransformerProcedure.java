package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Operators with a restricted/special rule set only applicable for top level
 * transformer procedures.
 */
public class TransformerProcedure extends Function {

    public TransformerProcedure(Name name, Sort sort, ImmutableArray<Sort> argSorts) {
        super(name, sort, argSorts);
    }

    public TransformerProcedure(Name name, Sort sort, Sort[] argSorts) {
        this(name, sort, new ImmutableArray<Sort>(argSorts));
    }

    public TransformerProcedure(Name name, Sort sort, Sort argSort) {
        this(name, sort, new ImmutableArray<Sort>(argSort));
    }
}