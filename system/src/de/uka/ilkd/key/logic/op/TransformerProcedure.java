// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

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
 * of the transformer procedure and not directly for its arguments, prohibiting any rule
 * applications to sub arguments as well as applications from outside such as update applications.
 * They work similar to the idea of 'Predicate Transformer Semantics' as introduced by Dijkstra in
 * "Guarded commands, nondeterminacy and formal derivation of programs".
 *
 * @author Michael Kirsten
 */
public class TransformerProcedure extends Function {

    // The template of the well-definedness transformer for terms.
    private static final TransformerProcedure WD_ANY =
            new TransformerProcedure(new Name("wd"), Sort.ANY);

    // The template of the well-definedness transformer for formulas.
    private static final TransformerProcedure WD_FORMULA =
            new TransformerProcedure(new Name("WD"), Sort.FORMULA);

    public TransformerProcedure(Name name, Sort sort, ImmutableArray<Sort> argSorts) {
        super(name, sort, argSorts, false);
    }

    public TransformerProcedure(Name name, Sort argSort) {
        this(name, Sort.FORMULA, new ImmutableArray<Sort>(argSort));
    }

    /**
     * Looks up the function namespace for a transformer procedure with the given
     * attributes, assuming it to be uniquely defined by its name. If none is found,
     * a new transformer procedure is created.
     * @param name name of the transformer procedure
     * @param sort sort of the transformer procedure
     * @param argSorts array of the procedure's argument sorts
     * @param services
     * @return the transformer procedure of interest
     */
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

    public static TransformerProcedure wdFormula(Services services) {
        return getTransformer(WD_FORMULA, services);
    }

    public static TransformerProcedure wdAny(Services services) {
        return getTransformer(WD_ANY, services);
    }

    /**
     * Takes a template for atransformer procedure and checks in the function
     * namespace, if an equivalent already exists. In this case, it returns
     * the found transformer procedure, otherwise it creates a new one.
     * @param t the template for a transformer procedure
     * @param services
     * @return the transformer procedure to be used
     */
    public static TransformerProcedure getTransformer(TransformerProcedure t,
                                                      Services services) {
        return getTransformer(t.name(), t.sort(), t.argSorts(), services);
    }

    /**
     * Examines a position for whether it is inside a transformer procedure.
     * @param pio A position in an occurrence of a term
     * @return true if inside a transformer procedure, false otherwise
     */
    public static boolean inTransformer(PosInOccurrence pio) {
        boolean trans = false;
        if (pio == null) {
            return false;
        }
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

    /**
     * Examines a position for whether it is inside a transformer procedure.
     * If this is the case, the found transformer procedure is returned.
     * @param pio A position in an occurrence of a term
     * @return the transformer procedure the position is in, null otherwise
     */
    public static TransformerProcedure getTransformer(PosInOccurrence pio) {
        if ( pio.posInTerm () != null ) {
            PIOPathIterator it = pio.iterator ();
            Operator        op;

            while ( it.next () != -1) {
                final Term t = it.getSubTerm ();
                op = t.op ();
                if (op instanceof TransformerProcedure)
                    return (TransformerProcedure)op;
            }
        }
        return null;
    }
}