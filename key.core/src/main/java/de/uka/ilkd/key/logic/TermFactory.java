package de.uka.ilkd.key.logic;

import java.util.*;
import java.util.stream.Collectors;

import org.jspecify.annotations.NonNull;

import de.uka.ilkd.key.logic.origin.OriginRef;
import de.uka.ilkd.key.logic.origin.OriginRefType;
import de.uka.ilkd.key.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableList;

/**
 * The TermFactory is the <em>only</em> way to create terms using constructors of class Term or any
 * of its subclasses. It is the only class that implements and may exploit knowledge about sub
 * classes of {@link Term}. All other classes of the system only know about terms what the
 * {@link Term} class offers them.
 *
 * This class is used to encapsulate knowledge about the internal term structures. See
 * {@link de.uka.ilkd.key.logic.TermBuilder} for more convenient methods to create terms.
 */
public final class TermFactory {


    private static final ImmutableArray<Term> NO_SUBTERMS = new ImmutableArray<Term>();
    private final Map<Term, Term> cache;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------


    public TermFactory() {
        this.cache = null;
    }

    public TermFactory(Map<Term, Term> cache) {
        this.cache = cache;
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------


    /**
     * Master method for term creation. Should be the only place where terms are created in the
     * entire system.
     */
    public Term createTerm(Operator op, ImmutableArray<Term> subs,
            ImmutableArray<QuantifiableVariable> boundVars, JavaBlock javaBlock,
            ImmutableArray<TermLabel> labels, ImmutableArray<OriginRef> originref) {
        if (op == null) {
            throw new TermCreationException("Given operator is null.");
        }

        if (subs == null || subs.isEmpty()) {
            subs = NO_SUBTERMS;
        }

        return doCreateTerm(op, subs, boundVars, javaBlock, labels, originref);
    }

    public Term createTerm(Operator op, ImmutableArray<Term> subs,
            ImmutableArray<QuantifiableVariable> boundVars, JavaBlock javaBlock,
            ImmutableArray<OriginRef> originref) {

        return createTerm(op, subs, boundVars, javaBlock, null, originref);
    }


    public Term createTerm(Operator op, Term[] subs, ImmutableArray<QuantifiableVariable> boundVars,
            JavaBlock javaBlock, ImmutableArray<OriginRef> originref) {
        return createTerm(op, createSubtermArray(subs), boundVars, javaBlock, null, originref);
    }


    public Term createTerm(Operator op, Term... subs) {
        return doCreateTerm(op, createSubtermArray(subs), null, null, null, null);
    }

    public Term createTerm(Operator op, Term[] subs, ImmutableArray<QuantifiableVariable> boundVars,
            JavaBlock javaBlock, ImmutableArray<TermLabel> labels, ImmutableArray<OriginRef> originref) {
        return createTerm(op, createSubtermArray(subs), boundVars, javaBlock, labels, originref);
    }

    public Term createTerm(Operator op, Term sub1, Term sub2, ImmutableArray<TermLabel> labels,
            ImmutableArray<OriginRef> originref) {
        return createTerm(op, new Term[] { sub1, sub2 }, null, null, labels, originref);
    }


    public Term createTerm(Operator op, ImmutableArray<TermLabel> labels, ImmutableArray<OriginRef> originref) {
        return createTerm(op, NO_SUBTERMS, null, null, labels, originref);
    }

    public @NonNull Term addOriginRef(Term base, OriginRef origref) {
        return addOriginRef(base, Collections.singleton(origref));
    }

    public @NonNull Term addOriginRef(Term base, ImmutableArray<OriginRef> origref) {
        return addOriginRef(base, origref.toList());
    }

    public @NonNull Term addOriginRef(Term base, Collection<OriginRef> origref) {
        var olist = base.getOriginRef().toList();
        var toadd = origref
            .stream()
            .filter(p -> olist.stream().noneMatch(q -> q.equalsModSource(p)))
            .collect(Collectors.toList());
        olist.addAll(toadd);

        Term newTerm = doCreateTerm(base.op(), base.subs(), base.boundVars(), base.javaBlock(),
                base.getLabels(), new ImmutableArray<>(olist));

        if (newTerm instanceof TermImpl && base instanceof TermImpl) {
            ((TermImpl) newTerm).setOrigin(base.getOrigin());
        }

        return newTerm;
    }

    public @NonNull Term setOriginRef(Term base, Collection<OriginRef> origref) {
        ImmutableArray<OriginRef> arr = new ImmutableArray<>(origref);
        Term newTerm = doCreateTerm(base.op(), base.subs(), base.boundVars(), base.javaBlock(), base.getLabels(), arr);

        if (newTerm instanceof TermImpl && base instanceof TermImpl) {
            ((TermImpl) newTerm).setOrigin(base.getOrigin());
        }

        return newTerm;
    }

    public @NonNull Term setOriginRefTypeRecursive(Term base, OriginRefType t, boolean force) {
        var origref = base.getOriginRef().toList();
        origref.replaceAll(o -> {
            if (o.Type == OriginRefType.LOOP_ANONUPDATE || o.Type == OriginRefType.OPERATION_ANONUPDATE) {
                return o; // leave heap_updates always alone
            }

            if (o.Type == OriginRefType.JAVA_STMT && !force) {
                return o;
            }

            return o.WithType(t);
        });

        if (origref.isEmpty() && force) {
            origref.add(new OriginRef(t, base));
        }

        var subs = base.subs().toList();

        subs.replaceAll(term -> setOriginRefTypeRecursive(term, t, false)); //TODO shouldn't this be (term, t, force) ?

        return doCreateTerm(base.op(), new ImmutableArray<>(subs), base.boundVars(),
            base.javaBlock(), base.getLabels(), new ImmutableArray<>(origref));
    }

    public @NonNull Term replaceOriginRefTypeRecursive(Term base, OriginRefType told, OriginRefType tnew) {
        var origref = base.getOriginRef().toList();
        for (int i = 0; i < origref.size(); i++) {
            if (origref.get(i).Type == told) {
                origref.set(i, origref.get(i).WithType(tnew));
            }
        }

        var subs = base.subs().toList();

        subs.replaceAll(term -> replaceOriginRefTypeRecursive(term, told, tnew));

        return doCreateTerm(base.op(), new ImmutableArray<>(subs), base.boundVars(),
                base.javaBlock(), base.getLabels(), new ImmutableArray<>(origref));
    }

    public @NonNull Term addOriginRefRecursive(Term base, OriginRef origref) {
        return addOriginRefRecursive(base, Collections.singleton(origref));
    }

    public @NonNull Term addOriginRefRecursive(Term base, Collection<OriginRef> origref) {
        var olist = base.getOriginRef().toList();
        var toadd = origref
                .stream()
                .filter(p -> olist.stream().noneMatch(q -> q.equalsModSource(p)))
                .collect(Collectors.toList());
        olist.addAll(toadd);

        var subs = base.subs().toList();
        subs.replaceAll(term -> addOriginRefRecursive(term, origref));

        Term newTerm = doCreateTerm(base.op(), new ImmutableArray<>(subs), base.boundVars(),
                base.javaBlock(), base.getLabels(), new ImmutableArray<>(origref));

        if (newTerm instanceof TermImpl && base instanceof TermImpl) {
            ((TermImpl) newTerm).setOrigin(base.getOrigin());
        }

        return newTerm;
    }


    public @NonNull Term replaceSubs(@NonNull Term base, Set<Term> subs) {
        return doCreateTerm(base.op(), new ImmutableArray<>(subs), base.boundVars(),
                base.javaBlock(), base.getLabels(), base.getOriginRef());
    }

    public @NonNull Term replaceSubs(@NonNull Term base, ImmutableArray<Term> subs) {
        return doCreateTerm(base.op(), subs, base.boundVars(),
                base.javaBlock(), base.getLabels(), base.getOriginRef());
    }

    // -------------------------------------------------------------------------
    // private interface
    // -------------------------------------------------------------------------

    private ImmutableArray<Term> createSubtermArray(Term[] subs) {
        return subs == null || subs.length == 0 ? NO_SUBTERMS : new ImmutableArray<Term>(subs);
    }

    private Term doCreateTerm(Operator op, ImmutableArray<Term> subs,
            ImmutableArray<QuantifiableVariable> boundVars, JavaBlock javaBlock,
            ImmutableArray<TermLabel> labels, ImmutableArray<OriginRef> originref) {
        final Term newTerm = (labels == null || labels.isEmpty()
                ? new TermImpl(op, subs, boundVars, javaBlock, (originref == null) ? (new ImmutableArray<>()) : originref)
                : new LabeledTermImpl(op, subs, boundVars, javaBlock, labels, (originref == null) ? (new ImmutableArray<>()) : originref)).checked();
        // Check if caching is possible. It is not possible if a non empty JavaBlock is available
        // in the term or in one of its children because the meta information like PositionInfos
        // may be different.
        if (cache != null && !newTerm.containsJavaBlockRecursive()) {
            Term term;
            synchronized (cache) {
                term = cache.get(newTerm);
            }
            if (term == null) {
                term = newTerm;
                synchronized (cache) {
                    cache.put(term, term);
                }
            }
            return term;
        } else {
            return newTerm;
        }
    }

    /**
     * Reduce the given list of terms into a one term by using the operator. The reduction is
     * left-associative. e.g., the result is {@code ((a op b) op c) op d }.
     *
     * @param junctor the left-associative operator to combine the terms together
     * @param terms a list of non-null temrs
     */
    public @NonNull Term createTerm(@NonNull Operator junctor, @NonNull List<Term> terms) {
        if (terms.size() == 1)
            return terms.get(0);
        else if (terms.size() == 2)
            return createTerm(junctor, terms.get(0), terms.get(1));
        final Optional<Term> reduce = terms.stream().reduce((a, b) -> createTerm(junctor, a, b));
        if (reduce.isPresent())
            return reduce.get();
        throw new IllegalArgumentException("list of terms is empty.");
    }
}
