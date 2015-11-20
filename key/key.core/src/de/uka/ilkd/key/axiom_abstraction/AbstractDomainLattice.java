package de.uka.ilkd.key.axiom_abstraction;

import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.isProvableWithSplitting;

import java.util.Iterator;

import de.uka.ilkd.key.axiom_abstraction.signanalysis.Top;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;

/**
 * An abstract domain is a countable lattice with a partial order relation and a
 * join operator. It supplies methods to abstract from a concrete domain to this
 * abstract domain, and for iterating through the domain elements, thereby
 * respecting the partial order.
 * 
 * @author Dominic Scheurer
 *
 * @param <AbstrDomElem>
 */
public abstract class AbstractDomainLattice implements
        PartialComparator<AbstractDomainElement>,
        Iterable<AbstractDomainElement> {

    /**
     * Time in milliseconds after which a proof attempt of a defining axiom
     * times out.
     */
    private static final int AXIOM_PROVE_TIMEOUT_MS = 1000;

    /**
     * Abstracts from a given element of the concrete domain by returning a
     * suitable abstract element. The returned abstract element should be as
     * precise as possible, that is there should not be a smaller abstract
     * element that also describes the concrete element.
     * 
     * @param elem
     *            Element to abstract from.
     * @return A suitable abstract domain element.
     */
    public AbstractDomainElement abstractFrom(SymbolicExecutionState state,
            Term term, Services services) {

        TermBuilder tb = services.getTermBuilder();

        Iterator<AbstractDomainElement> it = iterator();
        while (it.hasNext()) {
            AbstractDomainElement elem = it.next();

            Term axiom = elem.getDefiningAxiom(term, services);
            Term appl = tb.apply(state.first, axiom);
            Term toProve = tb.imp(state.second, appl);

            if (isProvableWithSplitting(toProve, services,
                    AXIOM_PROVE_TIMEOUT_MS)) {
                return elem;
            }
        }

        return Top.getInstance();
    }

    /**
     * A lattice join operation; finds an abstract element that is the least
     * upper bound of the set consisting of the elements a and b.
     * 
     * @param a
     *            First element to find the least upper bound for.
     * @param b
     *            Second element to find the least upper bound for.
     * @return The least upper bound of the set consisting of the elements a and
     *         b.
     */
    public abstract AbstractDomainElement join(AbstractDomainElement a,
            AbstractDomainElement b);

    @Override
    public PartialComparisonResult compare(AbstractDomainElement a,
            AbstractDomainElement b) {
        if (a.equals(b)) {
            return PartialComparisonResult.EQ;
        }

        AbstractDomainElement joinRes = join(a, b);
        if (joinRes.equals(a)) {
            return PartialComparisonResult.GTE;
        }
        else if (joinRes.equals(b)) {
            return PartialComparisonResult.LTE;
        }
        else {
            return PartialComparisonResult.UNDEF;
        }

    }

    /**
     * Iterates through the abstract domain elements of this abstract domain
     * starting by the smallest element; if an element b is returned by the
     * iterator after an element a, then either compare(a,b) == LTE, or
     * compare(a,b) == UNDEF must hold (i.e., b may not be smaller than a).
     */
    @Override
    public abstract Iterator<AbstractDomainElement> iterator();

}
