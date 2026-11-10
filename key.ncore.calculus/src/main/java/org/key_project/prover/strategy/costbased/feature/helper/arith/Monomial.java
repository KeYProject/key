/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature.helper.arith;

import java.math.BigInteger;
import java.util.Iterator;

import org.key_project.logic.Term;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

public class Monomial {
    public static final Monomial ONE = new Monomial(ImmutableList.nil(), BigInteger.ONE);
    protected final ImmutableList<Term> parts;
    protected final BigInteger coefficient;

    public Monomial(final ImmutableList<Term> parts, final BigInteger coefficient) {
        this.parts = parts;
        this.coefficient = coefficient;
    }

    /// @return the list of all terms that occur in `a` but not in `b`.
    /// multiplicity is treated as well here, so this is really difference of multisets
    private static ImmutableList<Term> difference(ImmutableList<Term> a, ImmutableList<Term> b) {
        ImmutableList<Term> res = a;
        final Iterator<Term> it = b.iterator();
        while (it.hasNext() && !res.isEmpty()) {
            res = res.removeFirst(it.next());
        }
        return res;
    }

    public Monomial setCoefficient(BigInteger c) {
        return new Monomial(parts, c);
    }

    public Monomial multiply(BigInteger c) {
        return new Monomial(parts, coefficient.multiply(c));
    }

    public Monomial multiply(Monomial m) {
        return new Monomial(parts.prepend(m.parts), coefficient.multiply(m.coefficient));
    }

    public Monomial addToCoefficient(BigInteger c) {
        return new Monomial(parts, coefficient.add(c));
    }

    /// @return true iff the monomial `this` divides the monomial `m`
    public boolean divides(Monomial m) {
        if (m.coefficient.signum() == 0) {
            return true;
        }
        if (this.coefficient.signum() == 0) {
            return false;
        }
        if (m.coefficient.remainder(this.coefficient).signum() != 0) {
            return false;
        }

        return Monomial.difference(this.parts, m.parts).isEmpty();
    }

    /// @return true iff the variables/parts of `this` subsume the variables of
    /// `m`, i.e., if each variable that occurs in `m` occurs in the
    /// same or a higher power in `this`
    public boolean variablesSubsume(Monomial m) {
        return this.parts.size() >= m.parts.size()
                && Monomial.difference(m.parts, this.parts).isEmpty();
    }

    public boolean variablesEqual(Monomial m) {
        return this.parts.size() == m.parts.size() && this.variablesSubsume(m);
    }

    public boolean variablesDisjoint(Monomial m) {
        return Monomial.difference(m.parts, this.parts).size() == m.parts.size();
    }

    /// @return true iff the coefficient of `m` can be made smaller (absolutely) by
    /// subtracting a multiple of `this`
    public boolean reducible(Monomial m) {
        final BigInteger a = m.coefficient;
        final BigInteger c = this.coefficient;

        if (compare(a.add(c), a) >= 0 && compare(a.subtract(c), a) >= 0) {
            return false;
        }

        return Monomial.difference(this.parts, m.parts).isEmpty();
    }

    /// @return the result of dividing the monomial `m` by the monomial `this`
    public Monomial reduce(Monomial m) {
        final BigInteger a = m.coefficient;
        final BigInteger c = this.coefficient;

        if (a.signum() == 0 || c.signum() == 0) {
            return new Monomial(ImmutableList.nil(), BigInteger.ZERO);
        }

        return new Monomial(Monomial.difference(m.parts, this.parts), divide(a, c));
    }

    /// @return the result of dividing the least common reducible (LCR) of monomial `m`
    /// and `this` by the monomial `this`
    public Monomial divideLCR(Monomial m) {
        assert coefficient.signum() != 0;
        assert m.coefficient.signum() != 0;

        final ImmutableList<Term> newParts = Monomial.difference(m.parts, this.parts);

        final BigInteger gcd = coefficient.abs().gcd(m.coefficient.abs());
        return new Monomial(newParts, m.coefficient.divide(gcd));

        /*
         * The code for groebner bases over the integers. We do not use that anymore and instead
         * compute groebner bases over the rationals (using pseudo-reduction)
         *
         * // in case one the coefficient of one of the monomials divides the other // coefficient:
         * simply make sure that the leading terms cancel out each // other. this makes the whole
         * algorithm a bit more robust concerning // signs if ( coefficient.remainder (
         * m.coefficient ).signum () == 0 ) return new Monomial ( newParts, BigInteger.ONE ); if (
         * m.coefficient.remainder ( coefficient ).signum () == 0 ) return new Monomial ( newParts,
         * m.coefficient.divide ( coefficient ) );
         *
         * BigInteger cofactor = cofactor ( coefficient, m.coefficient ); // (any)one of the two
         * cofactors has to be negated if ( coefficient.compareTo ( m.coefficient ) < 0 ) cofactor =
         * cofactor.negate ();
         *
         * return new Monomial ( newParts, cofactor );
         */
    }

    /// Extended Euclidean algorithm for computing cofactors. This satisfies the equation
    /// `gcd(a,b)=a\*cofactor(a,b)+b\*cofactor(b,a)`
    @SuppressWarnings("unused")
    private BigInteger cofactor(BigInteger v0, BigInteger v1) {
        final boolean neg = v0.signum() < 0;
        v0 = v0.abs();
        v1 = v1.abs();
        BigInteger c0 = BigInteger.ONE;
        BigInteger c1 = BigInteger.ZERO;
        while (v1.signum() != 0) {
            final BigInteger[] divRem = v0.divideAndRemainder(v1);
            v0 = v1;
            v1 = divRem[1];
            final BigInteger newC = c0.subtract(c1.multiply(divRem[0]));
            c0 = c1;
            c1 = newC;
        }
        if (neg) {
            return c0.negate();
        }
        return c0;
    }

    @Override
    public String toString() {
        final StringBuilder res = new StringBuilder();
        res.append(coefficient);

        for (Term part : parts) {
            res.append(" * ").append(part);
        }

        return res.toString();
    }

    @Override
    public boolean equals(@Nullable Object o) {
        if (o == this) {
            return true;
        }

        if (!(o instanceof Monomial m)) {
            return false;
        }

        if (!coefficient.equals(m.coefficient)) {
            return false;
        }
        if (parts.size() != m.parts.size()) {
            return false;
        }
        return Monomial.difference(parts, m.parts).isEmpty();
    }

    @Override
    public int hashCode() {
        int res = coefficient.hashCode();
        for (Term part : parts) {
            res += part.hashCode();
        }
        return res;
    }

    public BigInteger getCoefficient() {
        return coefficient;
    }

    public ImmutableList<Term> getParts() {
        return parts;
    }

    public boolean variablesAreCoprime(Monomial m) {
        return Monomial.difference(parts, m.parts).equals(parts);
    }

    /// TODO: this should also be used when comparing terms
    /// The reduction ordering on integers that is described in "A critical-pair/completion
    /// algorithm
    /// for finitely generated ideals in rings", with the difference that positive numbers are here
    /// considered as smaller than negative numbers (with the same absolute value)
    ///
    /// @return a negative number, zero, or a positive number, if `a` is smaller, equal to
    /// or greater than `b`
    public static int compare(BigInteger a, BigInteger b) {
        final int c = a.abs().compareTo(b.abs());
        if (c != 0) {
            return c;
        }
        return b.signum() - a.signum();
    }

    /// @return the result of dividing `a` by `c`, such that the remainder
    /// becomes minimal in the reduction ordering `LexPathOrdering.compare` on
    /// integers
    public static BigInteger divide(BigInteger a, BigInteger c) {
        final BigInteger[] divRem = a.divideAndRemainder(c);
        while (true) {
            // could be done more efficiently. but apparently the rounding
            // behaviour of BigInteger.divide for negative numbers is not
            // properly specified. or everything becomes very tedious ...

            final BigInteger newRem1 = divRem[1].subtract(c);
            if (compare(newRem1, divRem[1]) < 0) {
                divRem[0] = divRem[0].add(BigInteger.ONE);
                divRem[1] = newRem1;
                continue;
            }
            final BigInteger newRem2 = divRem[1].add(c);
            if (compare(newRem2, divRem[1]) < 0) {
                divRem[0] = divRem[0].subtract(BigInteger.ONE);
                divRem[1] = newRem2;
                continue;
            }

            return divRem[0];
        }
    }
}
