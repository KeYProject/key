/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature.helper.arith;

import java.math.BigInteger;
import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

public class Polynomial {
    /**
     * The polynomial expression of the BigInteger constant '0'.
     */
    public final static Polynomial ZERO =
        new Polynomial(BigInteger.ZERO, ImmutableList.nil());
    /**
     * The polynomial expression of the BigInteger constant '1'.
     */
    public final static Polynomial ONE =
        new Polynomial(BigInteger.ONE, ImmutableList.nil());
    /**
     * The BigInteger constant for the value '-1'.
     */
    private static final BigInteger MINUS_ONE = BigInteger.valueOf(-1);
    protected final BigInteger constantPart;
    protected final ImmutableList<Monomial> parts;

    public Polynomial(BigInteger constantPart, ImmutableList<Monomial> parts) {
        this.constantPart = constantPart;
        this.parts = parts;
    }

    /**
     * @return the list of all monomials that occur in <code>a</code> but not in <code>b</code>.
     *         multiplicity is treated as well here, so this is really difference of multisets
     */
    private static ImmutableList<Monomial> difference(ImmutableList<Monomial> a,
            ImmutableList<Monomial> b) {
        ImmutableList<Monomial> res = a;
        final Iterator<Monomial> it = b.iterator();
        while (it.hasNext() && !res.isEmpty()) {
            res = res.removeFirst(it.next());
        }
        return res;
    }

    public static ImmutableList<Monomial> addPart(ImmutableList<Monomial> oldParts, Monomial m) {
        if (m.getCoefficient().signum() == 0) {
            return oldParts;
        }
        final ImmutableList<Monomial> newParts = Polynomial.addPartHelp(oldParts, m);
        if (newParts != null) {
            return newParts;
        }
        return oldParts.prepend(m);
    }

    private static @Nullable ImmutableList<Monomial> addPartHelp(ImmutableList<Monomial> oldParts,
            Monomial m) {
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
        final ImmutableList<Monomial> res = Polynomial.addPartHelp(tail, m);
        if (res == null) {
            return null;
        }
        return res.prepend(head);
    }

    public Polynomial multiply(BigInteger c) {
        if (c.signum() == 0) {
            return ZERO;
        }
        ImmutableList<Monomial> newParts = ImmutableList.nil();
        for (Monomial part : parts) {
            newParts = newParts.prepend(part.multiply(c));
        }

        return new Polynomial(constantPart.multiply(c), newParts);
    }

    public Polynomial multiply(Monomial m) {
        if (m.getCoefficient().signum() == 0) {
            return ZERO;
        }

        ImmutableList<Monomial> newParts = ImmutableList.nil();
        for (Monomial part : parts) {
            newParts = newParts.prepend(part.multiply(m));
        }

        if (m.getParts().isEmpty()) {
            return new Polynomial(constantPart.multiply(m.getCoefficient()), newParts);
        }

        newParts = Polynomial.addPart(newParts, m.multiply(constantPart));
        return new Polynomial(BigInteger.ZERO, newParts);
    }

    public Polynomial add(BigInteger c) {
        return new Polynomial(constantPart.add(c), parts);
    }

    public Polynomial sub(Polynomial p) {
        final BigInteger newConst = getConstantTerm().subtract(p.getConstantTerm());
        ImmutableList<Monomial> newParts = parts;
        for (Monomial monomial : p.getParts()) {
            newParts = Polynomial.addPart(newParts, monomial.multiply(MINUS_ONE));
        }
        return new Polynomial(newConst, newParts);
    }

    public Polynomial add(Monomial m) {
        if (m.getParts().isEmpty()) {
            return new Polynomial(constantPart.add(m.getCoefficient()), parts);
        }

        return new Polynomial(constantPart, Polynomial.addPart(parts, m));
    }

    public Polynomial add(Polynomial p) {
        final BigInteger newConst = getConstantTerm().add(p.getConstantTerm());
        ImmutableList<Monomial> newParts = parts;
        for (Monomial monomial : p.getParts()) {
            newParts = Polynomial.addPart(newParts, monomial);
        }
        return new Polynomial(newConst, newParts);
    }

    /**
     * @return the greatest common divisor of the coefficients of the monomials of this polynomial.
     *         The constant part of the polynomial is not taken into account. If there are no
     *         monomials (apart from the constant term), the result is <code>BigInteger.ZERO</code>
     */
    public BigInteger coeffGcd() {
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
    public boolean valueLess(Polynomial p) {
        if (!sameParts(p)) {
            return false;
        }
        return constantPart.compareTo(p.constantPart) < 0;
    }

    /**
     * @return <code>true</code> if the value of <code>this</code> will always be equal to the value
     *         of <code>p</code> (i.e., same monomials and same constant part)
     */
    public boolean valueEq(Polynomial p) {
        if (!sameParts(p)) {
            return false;
        }
        return constantPart.equals(p.constantPart);
    }

    public boolean valueUneq(Polynomial p) {
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
    public boolean valueLeq(Polynomial p) {
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

    public boolean sameParts(Polynomial p) {
        if (parts.size() != p.parts.size()) {
            return false;
        }
        return Polynomial.difference(parts, p.parts).isEmpty();
    }

    @Override
    public String toString() {
        final StringBuilder res = new StringBuilder();
        res.append(constantPart);

        for (Monomial part : parts) {
            res.append(" + ").append(part);
        }

        return res.toString();
    }

    public BigInteger getConstantTerm() {
        return constantPart;
    }

    public ImmutableList<Monomial> getParts() {
        return parts;
    }
}
