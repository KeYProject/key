/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;
import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Operator;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.key_project.util.LRUCache;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Class for analysing and modifying polynomial expressions over the integers
 */
public class Polynomial {

    /**
     * The polynomial expression of the BigInteger constant '0'.
     */
    public final static Polynomial ZERO =
        new Polynomial(ImmutableSLList.nil(), BigInteger.ZERO);
    /**
     * The polynomial expression of the BigInteger constant '1'.
     */
    public final static Polynomial ONE =
        new Polynomial(ImmutableSLList.nil(), BigInteger.ONE);

    /**
     * The BigInteger constant for the value '-1'.
     */
    private static final BigInteger MINUS_ONE = BigInteger.valueOf(-1);

    private final BigInteger constantPart;
    private final ImmutableList<Monomial> parts;

    private Polynomial(ImmutableList<Monomial> parts, BigInteger constantPart) {
        this.parts = parts;
        this.constantPart = constantPart;
    }

    public static @NonNull Polynomial create(Term polyTerm, @NonNull Services services) {
        final LRUCache<Term, Polynomial> cache = services.getCaches().getPolynomialCache();
        polyTerm = TermLabelManager.removeIrrelevantLabels(polyTerm, services);

        Polynomial res;
        synchronized (cache) {
            res = cache.get(polyTerm);
        }

        if (res == null) {
            res = createHelp(polyTerm, services);
            synchronized (cache) {
                cache.put(polyTerm, res);
            }
        }
        return res;
    }

    private static @NonNull Polynomial createHelp(@NonNull Term polynomial, @NonNull Services services) {
        final Analyser a = new Analyser(services);
        a.analyse(polynomial);
        return new Polynomial(a.parts, a.constantPart);
    }

    public @NonNull Polynomial multiply(@NonNull BigInteger c) {
        if (c.signum() == 0) {
            return new Polynomial(ImmutableSLList.nil(), BigInteger.ZERO);
        }
        ImmutableList<Monomial> newParts = ImmutableSLList.nil();
        for (Monomial part : parts) {
            newParts = newParts.prepend(part.multiply(c));
        }

        return new Polynomial(newParts, constantPart.multiply(c));
    }

    public @NonNull Polynomial multiply(@NonNull Monomial m) {
        if (m.getCoefficient().signum() == 0) {
            return new Polynomial(ImmutableSLList.nil(), BigInteger.ZERO);
        }

        ImmutableList<Monomial> newParts = ImmutableSLList.nil();
        for (Monomial part : parts) {
            newParts = newParts.prepend(part.multiply(m));
        }

        if (m.getParts().isEmpty()) {
            return new Polynomial(newParts, constantPart.multiply(m.getCoefficient()));
        }

        newParts = addPart(newParts, m.multiply(constantPart));
        return new Polynomial(newParts, BigInteger.ZERO);
    }

    public @NonNull Polynomial add(BigInteger c) {
        return new Polynomial(parts, constantPart.add(c));
    }

    public @NonNull Polynomial sub(@NonNull Polynomial p) {
        final BigInteger newConst = getConstantTerm().subtract(p.getConstantTerm());
        ImmutableList<Monomial> newParts = parts;
        for (Monomial monomial : p.getParts()) {
            newParts = addPart(newParts, monomial.multiply(MINUS_ONE));
        }
        return new Polynomial(newParts, newConst);
    }

    public @NonNull Polynomial add(@NonNull Monomial m) {
        if (m.getParts().isEmpty()) {
            return new Polynomial(parts, constantPart.add(m.getCoefficient()));
        }

        return new Polynomial(addPart(parts, m), constantPart);
    }

    public @NonNull Polynomial add(@NonNull Polynomial p) {
        final BigInteger newConst = getConstantTerm().add(p.getConstantTerm());
        ImmutableList<Monomial> newParts = parts;
        for (Monomial monomial : p.getParts()) {
            newParts = addPart(newParts, monomial);
        }
        return new Polynomial(newParts, newConst);
    }

    /**
     * @return the greatest common divisor of the coefficients of the monomials of this polynomial.
     *         The constant part of the polynomial is not taken into account. If there are no
     *         monomials (apart from the constant term), the result is <code>BigInteger.ZERO</code>
     */
    public @NonNull BigInteger coeffGcd() {
        BigInteger res = BigInteger.ZERO;
        for (Monomial part : parts) {
            res = res.gcd(part.getCoefficient());
        }
        return res;
    }

    /**
     * @return <code>true</code> if the value of <code>this</code> will always be less than the
     *         value of <code>p</code> (i.e., same monomials, but the constant part is less or
     *         equal)
     */
    public boolean valueLess(@NonNull Polynomial p) {
        if (!sameParts(p)) {
            return false;
        }
        return constantPart.compareTo(p.constantPart) < 0;
    }

    /**
     * @return <code>true</code> if the value of <code>this</code> will always be equal to the value
     *         of <code>p</code> (i.e., same monomials and same constant part)
     */
    public boolean valueEq(@NonNull Polynomial p) {
        if (!sameParts(p)) {
            return false;
        }
        return constantPart.equals(p.constantPart);
    }

    public boolean valueUneq(@NonNull Polynomial p) {
        if (!sameParts(p)) {
            return false;
        }
        return !constantPart.equals(p.constantPart);
    }

    public boolean valueEq(BigInteger c) {
        if (!parts.isEmpty()) {
            return false;
        }
        return constantPart.equals(c);
    }

    public boolean valueUneq(BigInteger c) {
        if (!parts.isEmpty()) {
            return false;
        }
        return !constantPart.equals(c);
    }

    /**
     * @return <code>true</code> if the value of <code>this</code> will always be less or equal than
     *         the value of <code>p</code> (i.e., same monomials, but the constant part is less or
     *         equal)
     */
    public boolean valueLeq(@NonNull Polynomial p) {
        if (!sameParts(p)) {
            return false;
        }
        return constantPart.compareTo(p.constantPart) <= 0;
    }

    public boolean valueLess(BigInteger c) {
        if (!parts.isEmpty()) {
            return false;
        }
        return constantPart.compareTo(c) < 0;
    }

    public boolean valueGeq(BigInteger c) {
        if (!parts.isEmpty()) {
            return false;
        }
        return constantPart.compareTo(c) >= 0;
    }

    public boolean sameParts(@NonNull Polynomial p) {
        if (parts.size() != p.parts.size()) {
            return false;
        }
        return difference(parts, p.parts).isEmpty();
    }

    /**
     * Creates a term from this polynomial expression.
     *
     * @param services the services object
     * @return the resulting term
     */
    public @NonNull Term toTerm(@NonNull Services services) {
        final Operator add = services.getTypeConverter().getIntegerLDT().getAdd();
        Term res = null;

        final Iterator<Monomial> it = parts.iterator();
        if (it.hasNext()) {
            res = it.next().toTerm(services);
            while (it.hasNext()) {
                res = services.getTermFactory().createTerm(add, res, it.next().toTerm(services));
            }
        }

        final Term cTerm = services.getTermBuilder().zTerm(constantPart.toString());

        if (res == null) {
            res = cTerm;
        } else if (!BigInteger.ZERO.equals(constantPart)) {
            res = services.getTermFactory().createTerm(add, cTerm, res);
        }

        return res;
    }

    @Override
    public @NonNull String toString() {
        final StringBuilder res = new StringBuilder();
        res.append(constantPart);

        for (Monomial part : parts) {
            res.append(" + ").append(part);
        }

        return res.toString();
    }

    private static class Analyser {
        public @NonNull BigInteger constantPart = BigInteger.ZERO;
        public @NonNull ImmutableList<Monomial> parts = ImmutableSLList.nil();
        private final @NonNull Services services;
        private final @NonNull TypeConverter tc;
        private final @NonNull Operator numbers, add;

        public Analyser(final @NonNull Services services) {
            this.services = services;
            this.tc = services.getTypeConverter();
            final IntegerLDT intLDT = tc.getIntegerLDT();
            numbers = intLDT.getNumberSymbol();
            add = intLDT.getAdd();
        }

        public void analyse(@NonNull Term polynomial) {
            final Operator op = polynomial.op();
            if (op == add) {
                analyse(polynomial.sub(0));
                analyse(polynomial.sub(1));
            } else if (op == numbers) {
                final BigInteger c = new BigInteger(
                    AbstractTermTransformer.convertToDecimalString(polynomial, services));
                constantPart = constantPart.add(c);
            } else {
                parts = addPart(parts, Monomial.create(polynomial, services));
            }
        }
    }

    /**
     * @return the list of all monomials that occur in <code>a</code> but not in <code>b</code>.
     *         multiplicity is treated as well here, so this is really difference of multisets
     */
    private static ImmutableList<Monomial> difference(ImmutableList<Monomial> a,
                                                      @NonNull ImmutableList<Monomial> b) {
        ImmutableList<Monomial> res = a;
        final Iterator<Monomial> it = b.iterator();
        while (it.hasNext() && !res.isEmpty()) {
            res = res.removeFirst(it.next());
        }
        return res;
    }

    private static @NonNull ImmutableList<Monomial> addPart(@NonNull ImmutableList<Monomial> oldParts, @NonNull Monomial m) {
        if (m.getCoefficient().signum() == 0) {
            return oldParts;
        }
        final ImmutableList<Monomial> newParts = addPartHelp(oldParts, m);
        if (newParts != null) {
            return newParts;
        }
        return oldParts.prepend(m);
    }

    private static @Nullable ImmutableList<Monomial> addPartHelp(@NonNull ImmutableList<Monomial> oldParts,
                                                                 @NonNull Monomial m) {
        if (oldParts.isEmpty()) {
            return null;
        }
        final Monomial head = oldParts.head();
        final ImmutableList<Monomial> tail = oldParts.tail();
        if (head.variablesEqual(m)) {
            final Monomial newHead = head.addToCoefficient(m.getCoefficient());
            if (newHead.getCoefficient().signum() == 0) {
                return tail;
            }
            return tail.prepend(newHead);
        }
        final ImmutableList<Monomial> res = addPartHelp(tail, m);
        if (res == null) {
            return null;
        }
        return res.prepend(head);
    }

    public BigInteger getConstantTerm() {
        return constantPart;
    }

    public ImmutableList<Monomial> getParts() {
        return parts;
    }
}
