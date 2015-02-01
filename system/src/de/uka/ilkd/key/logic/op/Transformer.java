// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Functions with a restricted/special rule set only applicable for the top level
 * of the term transformer and not directly for its arguments, prohibiting any rule
 * applications to sub arguments as well as applications from outside such as update applications.
 * They work similar to the idea of 'Predicate Transformer Semantics' as introduced by Dijkstra in
 * "Guarded commands, nondeterminacy and formal derivation of programs".
 *
 * Note that in the taclets, arguments such as "a -> b" need to be written as "(a -> b)", in order
 * to let the parser know that the argument is "a -> b" and not "a" followed by a syntactic error.
 *
 * @author Michael Kirsten
 */
public class Transformer extends Function {

    public Transformer(Name name, Sort sort, ImmutableArray<Sort> argSorts) {
        super(name, sort, argSorts, false);
    }

    public Transformer(Name name, Sort argSort) {
        this(name, Sort.FORMULA, new ImmutableArray<Sort>(argSort));
    }

    /**
     * Looks up the function namespace for a term transformer with the given
     * attributes, assuming it to be uniquely defined by its name. If none is found,
     * a new term transformer is created.
     * @param name name of the term transformer
     * @param sort sort of the term transformer
     * @param argSorts array of the transformer's argument sorts
     * @param services
     * @return the term transformer of interest
     */
    public static Transformer getTransformer(Name name,
                                                      Sort sort,
                                                      ImmutableArray<Sort> argSorts,
                                                      TermServices services) {
        final Named f = services.getNamespaces().functions().lookup(name);
        if (f != null && f instanceof Transformer) {
            Transformer t = (Transformer)f;
            assert t.sort() == sort;
            assert t.argSorts().size() == argSorts.size();
            return t;
        }
        return new Transformer(name, sort, argSorts);
    }

    /**
     * Takes a template for a term transformer and checks in the function
     * namespace, whether an equivalent already exists. If this is the case,
     * it returns the found transformer, otherwise it creates a new one.
     * @param t the template for a term transformer
     * @param services
     * @return the term transformer to be used
     */
    public static Transformer getTransformer(Transformer t,
                                                      TermServices services) {
        return getTransformer(t.name(), t.sort(), t.argSorts(), services);
    }

    /**
     * Examines a position for whether it is inside a term transformer.
     * @param pio A position in an occurrence of a term
     * @return true if inside a term transformer, false otherwise
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
                trans = op instanceof Transformer;
            }
        }
        return trans;
    }

    /**
     * Examines a position for whether it is inside a term transformer.
     * If this is the case, the found term transformer is returned.
     * @param pio A position in an occurrence of a term
     * @return the term transformer the position is in, null otherwise
     */
    public static Transformer getTransformer(PosInOccurrence pio) {
        if ( pio.posInTerm () != null ) {
            PIOPathIterator it = pio.iterator ();
            Operator        op;

            while ( it.next () != -1) {
                final Term t = it.getSubTerm ();
                op = t.op ();
                if (op instanceof Transformer)
                    return (Transformer)op;
            }
        }
        return null;
    }
}