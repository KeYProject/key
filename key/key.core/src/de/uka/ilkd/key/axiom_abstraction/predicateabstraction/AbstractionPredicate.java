// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2015 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.axiom_abstraction.predicateabstraction;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.naming.NameAlreadyBoundException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.io.OutputStreamProofSaver;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.joinrule.JoinRuleUtils;

/**
 * Interface for predicates used for predicate abstraction. An abstraction
 * predicate is a mapping from program variables or constants to formulae
 * instantiated for the respective variable.
 *
 * @author Dominic Scheurer
 */
public abstract class AbstractionPredicate implements Function<Term, Term>,
        Named {

    /**
     * The sort for the argument of this {@link AbstractionPredicate}.
     */
    private Sort argSort;

    /**
     * The predicate term. Contains a placeholder ({@link #placeholderVariable})
     * which is to be replaced by the concrete argument of the predicate.
     * <p>
     * 
     * This field is needed to save proofs with abstraction predicates.
     */
    private Term predicateFormWithPlaceholder = null;

    /**
     * The placeholder variable occurring in
     * {@link #predicateFormWithPlaceholder} which is to be replaced by the
     * concrete argument of the predicate.
     * <p>
     * 
     * This field is needed to save proofs with abstraction predicates.s
     */
    private LocationVariable placeholderVariable = null;

    /**
     * Creates a new {@link AbstractionPredicate}. Constructor is hidden since
     * elements fo this class should be created by the factory method
     * {@link #create(String, Function)}.
     * 
     * @param argSort
     *            The expected sort for the arguments of the predicate.
     */
    private AbstractionPredicate(Sort argSort) {
        this.argSort = argSort;
    }

    /**
     * @return The placeholder variable and the function term that this
     *         predicate has been constructed with.
     */
    public Pair<LocationVariable, Term> getPredicateFormWithPlaceholder() {
        return new Pair<LocationVariable, Term>(placeholderVariable,
                predicateFormWithPlaceholder);
    }

    /**
     * Creates a new {@link AbstractionPredicate} with the given name and
     * mapping. You may use nice Java 8 lambdas for the second argument!
     * <p>
     * 
     * This method has been created for testing purposes; you should rather user
     * {@link #create(Term, LocationVariable, Services)} instead.
     * 
     * @param argSort
     *            The expected sort for the arguments of the predicate.
     * @param mapping
     *            The mapping from input terms of the adequate type to formulae,
     *            e.g. "(Term input) -> (tb.gt(input, tb.zero()))" where tb is a
     *            {@link TermBuilder}.
     * @param services
     *            The services object.
     * @return An abstraction predicate encapsulating the given mapping.
     */
    public static AbstractionPredicate create(final Sort argSort,
            final Function<Term, Term> mapping, Services services) {
        LocationVariable placeholder =
                JoinRuleUtils.getFreshLocVariableForPrefix("_ph", argSort,
                        services);

        return create(
                mapping.apply(services.getTermBuilder().var(placeholder)),
                placeholder, services);
    }

    /**
     * Creates a new {@link AbstractionPredicate} for the given predicate. The
     * predicate should contain the given placeholder variable, which is
     * substituted by the argument supplied to the generated mapping.
     * 
     * @param predicate
     *            The predicate formula containing the placeholder.
     * @param placeholder
     *            The placeholder to replace in the generated mapping.
     * @param services
     *            The services object.
     * @return An abstraction predicate mapping terms to the predicate with the
     *         placeholder substituted by the respective term.
     */
    public static AbstractionPredicate create(final Term predicate,
            final LocationVariable placeholder, Services services) {
        final TermBuilder tb = services.getTermBuilder();
        final TermFactory tf = services.getTermFactory();
        final Sort fInputSort = placeholder.sort();

        AbstractionPredicate result = new AbstractionPredicate(fInputSort) {
            private final Name name = new Name("abstrPred_"
                    + predicate.op().toString());
            private Function<Term, Term> mapping = null;

            @Override
            public Term apply(Term input) {
                if (mapping == null) {
                    mapping =
                            (Term param) -> {
                                if (param.sort() != fInputSort) {
                                    throw new IllegalArgumentException(
                                            "Input must be of sort \""
                                                    + fInputSort
                                                    + "\", given: \""
                                                    + param.sort() + "\".");
                                }

                                return OpReplacer.replace(tb.var(placeholder),
                                        param, predicate, tf);
                            };
                }

                return mapping.apply(input);
            }

            @Override
            public Name name() {
                return name;
            }
        };

        result.predicateFormWithPlaceholder = predicate;
        result.placeholderVariable = placeholder;

        return result;
    }

    /**
     * @return The sort of this predicate's argument.
     */
    public Sort getArgSort() {
        return argSort;
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.util.function.Function#apply(java.lang.Object)
     */
    @Override
    public abstract Term apply(Term t);

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return name().toString();
    }

    /**
     * Returns a parseable String representation of this abstraction predicate
     * of the form "('[[TYPE]] [[PLACEHOLDER]]', '[[PREDICATE]]')".
     * 
     * @param services
     *            The services object.
     * @return A parseable String representation of this predicate.
     */
    public String toParseableString(final Services services) {
        StringBuilder sb = new StringBuilder();
        Pair<LocationVariable, Term> predicateFormWithPlaceholder =
                getPredicateFormWithPlaceholder();

        sb.append("(")
                .append("'")
                .append(predicateFormWithPlaceholder.first.sort())
                .append(" ")
                .append(predicateFormWithPlaceholder.first)
                .append("', '")
                .append(OutputStreamProofSaver
                        .escapeCharacters(OutputStreamProofSaver.printAnything(
                                predicateFormWithPlaceholder.second, services,
                                false).toString())).append("')");

        return sb.toString();
    }

    /**
     * TODO: Document.
     * 
     * @param s
     * @param services
     * @return
     * @throws ParserException If there is a syntax error.
     * @throws NameAlreadyBoundException If the given placeholder is already known to the system.
     * @throws SortNotKnownException If the given sort is not known to the system.
     */
    public static List<AbstractionPredicate> fromString(final String s,
            final Services services) throws ParserException {
        final ArrayList<AbstractionPredicate> result =
                new ArrayList<AbstractionPredicate>();

        Pattern p = Pattern.compile("\\('(.+?)', '(.+?)'\\)");
        Matcher m = p.matcher(s);

        boolean matched = false;
        while (m.find()) {
            matched = true;

            for (int i = 1; i < m.groupCount(); i += 2) {
                assert i + 1 <= m.groupCount() : "Wrong format of join abstraction predicates: "
                        + "There should always be pairs of placeholders and predicate terms.";

                final String phStr = m.group(i);
                final String predStr = m.group(i + 1);

                // Parse the placeholder
                Pair<Sort, Name> ph = null;
                ph = JoinRuleUtils.parsePlaceholder(phStr, false, services);

                // Add placeholder to namespaces, if necessary
                if (services.getNamespaces().variables().lookup(ph.second) == null) {
                    services.getNamespaces()
                            .variables()
                            .add(new LocationVariable(new ProgramElementName(
                                    ph.second.toString()), ph.first));
                }

                // Parse the predicate
                result.add(JoinRuleUtils.parsePredicate(predStr,
                        JoinRuleUtils.singletonArrayList(ph), services));
            }
        }

        if (!matched) {
            throw new ParserException(
                    "Wrong format of join abstraction predicates", null);
        }

        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof AbstractionPredicate)) {
            return false;
        }

        final AbstractionPredicate otherPred = (AbstractionPredicate) obj;

        return otherPred.placeholderVariable.equals(placeholderVariable)
                && otherPred.predicateFormWithPlaceholder
                        .equals(predicateFormWithPlaceholder);
    }

}
