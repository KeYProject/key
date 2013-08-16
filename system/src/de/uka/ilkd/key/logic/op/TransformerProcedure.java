package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Operators with a restricted/special rule set only applicable for top level
 * transformer procedures.
 */
public class TransformerProcedure extends Function {

    public TransformerProcedure(Name name, Sort sort, ImmutableArray<Sort> argSorts) {
        super(name, sort, argSorts, false);
    }

    public TransformerProcedure(Name name, Sort sort, Sort[] argSorts) {
        this(name, sort, new ImmutableArray<Sort>(argSorts));
    }

    public TransformerProcedure(Name name, Sort sort, Sort argSort) {
        this(name, sort, new ImmutableArray<Sort>(argSort));
    }

    public static TransformerProcedure getTransformer(Name name,
                                                      Sort sort,
                                                      ImmutableArray<Sort> argSorts,
                                                      Services services) {
        final Named f = services.getNamespaces().functions().lookup(name);
        if (f != null && f instanceof TransformerProcedure) {
            TransformerProcedure t = (TransformerProcedure)f;
            assert t.sort() == sort;
            assert t.argSorts().size() == argSorts.size();
            return t;
        }
        return new TransformerProcedure(name, sort, argSorts);
    }

    public static TransformerProcedure getTransformer(Name name,
                                                      Sort argSort,
                                                      Services services) {
        return getTransformer(name,
                              Sort.FORMULA,
                              new ImmutableArray<Sort>(argSort),
                              services);
    }

    public static boolean inTransformer(PosInOccurrence pio) {
        boolean trans = false;
        if ( pio.posInTerm () != null ) {
            PIOPathIterator it = pio.iterator ();
            Operator        op;

            while ( it.next () != -1 && !trans) {
                final Term t = it.getSubTerm ();
                op = t.op ();
                trans = op instanceof TransformerProcedure;
            }
        }
        return trans;
    }
}