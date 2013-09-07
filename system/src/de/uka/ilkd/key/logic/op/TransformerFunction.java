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
 * Functions with a restricted/special rule set only applicable for the top level
 * of the transformer function and not directly for its arguments.
 *
 * @author Michael Kirsten
 */
public class TransformerFunction extends Function {

    // The template of the well-definedness transformer for terms. 
    private static final TransformerFunction WD_ANY =
            new TransformerFunction(new Name("wd"), Sort.ANY);

    // The template of the well-definedness transformer for formulas.
    private static final TransformerFunction WD_FORMULA =
            new TransformerFunction(new Name("WD"), Sort.FORMULA);

    public TransformerFunction(Name name, Sort sort, ImmutableArray<Sort> argSorts) {
        super(name, sort, argSorts, false);
    }

    public TransformerFunction(Name name, Sort argSort) {
        this(name, Sort.FORMULA, new ImmutableArray<Sort>(argSort));
    }

    public static TransformerFunction getTransformer(Name name,
                                                      Sort sort,
                                                      ImmutableArray<Sort> argSorts,
                                                      Services services) {
        final Named f = services.getNamespaces().functions().lookup(name);
        if (f != null && f instanceof TransformerFunction) {
            TransformerFunction t = (TransformerFunction)f;
            assert t.sort() == sort;
            assert t.argSorts().size() == argSorts.size();
            return t;
        }
        return new TransformerFunction(name, sort, argSorts);
    }

    public static TransformerFunction wdFormula(Services services) {
        return getTransformer(WD_FORMULA, services);
    }

    public static TransformerFunction wdAny(Services services) {
        return getTransformer(WD_ANY, services);
    }

    public static TransformerFunction getTransformer(TransformerFunction t,
                                                      Services services) {
        return getTransformer(t.name(), t.sort(), t.argSorts(), services);
    }

    public static boolean inTransformer(PosInOccurrence pio) {
        boolean trans = false;
        if ( pio.posInTerm () != null ) {
            PIOPathIterator it = pio.iterator ();
            Operator        op;

            while ( it.next () != -1 && !trans) {
                final Term t = it.getSubTerm ();
                op = t.op ();
                trans = op instanceof TransformerFunction;
            }
        }
        return trans;
    }
}