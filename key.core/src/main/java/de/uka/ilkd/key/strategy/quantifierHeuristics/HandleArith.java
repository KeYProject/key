/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.metaconstruct.arith.Polynomial;

import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.util.LRUCache;
import org.key_project.util.collection.Pair;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;

/**
 * This class is used to prove some simple arithmetic problem which are {@code a==b}, {@code a>=b},
 * {@code a<=b}; Besides it can be used to prove that {@code a>=b} or {@code a<=b} by
 * knowing that {@code c>=d} or {@code c<=d;}
 *
 */
public class HandleArith {

    private HandleArith() {}

    /**
     * try to prove atom by using polynomial
     *
     * @param problem
     * @return <code>trueT</code> if if formu is proved to true, <code>falseT</code> if false, and
     *         <code>problem</code> if it cann't be proved.
     */
    public static JTerm provedByArith(JTerm problem, Services services) {
        final LRUCache<JTerm, JTerm> provedByArithCache =
            services.getCaches().getProvedByArithFstCache();
        JTerm result;
        synchronized (provedByArithCache) {
            result = provedByArithCache.get(problem);
        }
        if (result != null) {
            return result;
        }

        TermBuilder tb = services.getTermBuilder();
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();

        final JTerm trueT = tb.tt();
        final JTerm falseT = tb.ff();

        final JTerm arithTerm = formatArithTerm(problem, tb, integerLDT, services.getCaches());
        if (arithTerm.equalsModProperty(falseT, IRRELEVANT_TERM_LABELS_PROPERTY)) {
            result = provedArithEqual(problem, tb, services);
            putInTermCache(provedByArithCache, problem, result);
            return result;
        }
        Polynomial poly1 = Polynomial.create(arithTerm.sub(0), services);
        Polynomial poly2 = Polynomial.create(arithTerm.sub(1), services);

        if (poly2.valueLeq(poly1)) {
            putInTermCache(provedByArithCache, problem, trueT);
            return trueT;
        }
        if (poly1.valueLess(poly2)) {
            putInTermCache(provedByArithCache, problem, falseT);
            return falseT;
        }
        putInTermCache(provedByArithCache, problem, problem);
        return problem;
    }



    private static void putInTermCache(final LRUCache<JTerm, JTerm> provedByArithCache,
            final JTerm key, final JTerm value) {
        synchronized (provedByArithCache) {
            provedByArithCache.put(key, value);
        }
    }

    /**
     * @param problem
     * @return true if atom.sub(0) is euqual to atom.sub(1), false if not equal, else return atom
     */
    private static JTerm provedArithEqual(JTerm problem, TermBuilder tb, Services services) {
        final JTerm trueT = tb.tt();
        final JTerm falseT = tb.ff();

        boolean temp = true;
        JTerm pro = problem;
        Operator op = pro.op();
        // may be here we should check wehre sub0 and sub1 is integer.
        while (op == Junctor.NOT) {
            pro = pro.sub(0);
            op = pro.op();
            temp = !temp;
        }
        if (op == Equality.EQUALS) {
            JTerm sub0 = pro.sub(0);
            JTerm sub1 = pro.sub(1);
            Polynomial poly1 = Polynomial.create(sub0, services);
            Polynomial poly2 = Polynomial.create(sub1, services);
            boolean gt = poly2.valueLeq(poly1);
            boolean lt = poly1.valueLeq(poly2);
            if (gt && lt) {
                return temp ? trueT : falseT;
            }
            if (gt || lt) {
                return temp ? falseT : trueT;
            }
        }
        return problem;
    }


    /**
     * Try to prove problem by know that axiom is true. The idea is that we know a>=b(axiom),we want
     * to prove c>=d(problem). It is enough to prove that c+b>=a+d which means c>=d is true. or we
     * prove that !(c>=d) which is d>=c+1 is true. This means c>= d is false;
     *
     * @param problem
     * @param axiom
     * @return trueT if true, falseT if false, and atom if can't be prove;
     */
    public static JTerm provedByArith(JTerm problem, JTerm axiom, Services services) {
        final Pair<JTerm, JTerm> key = new Pair<>(problem, axiom);
        final LRUCache<Pair<JTerm, JTerm>, JTerm> provedByArithCache =
            services.getCaches().getProvedByArithSndCache();
        JTerm result;
        synchronized (provedByArithCache) {
            result = provedByArithCache.get(key);
        }
        if (result != null) {
            return result;
        }

        final TermBuilder tb = services.getTermBuilder();
        final IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        final ServiceCaches caches = services.getCaches();

        final JTerm cd = formatArithTerm(problem, tb, integerLDT, caches);
        final JTerm ab = formatArithTerm(axiom, tb, integerLDT, caches);
        final JTerm trueT = tb.tt();
        final JTerm falseT = tb.ff();

        if (cd.op() == Junctor.FALSE || ab.op() == Junctor.FALSE) {
            synchronized (provedByArithCache) {
                provedByArithCache.put(key, problem);
            }
            return problem;
        }
        Function addfun = integerLDT.getAdd();
        JTerm arithTerm =
            tb.geq(tb.func(addfun, cd.sub(0), ab.sub(1)), tb.func(addfun, ab.sub(0), cd.sub(1)));
        JTerm res = provedByArith(arithTerm, services);
        if (res.op() == Junctor.TRUE) {
            synchronized (provedByArithCache) {
                provedByArithCache.put(key, trueT);
            }
            return trueT;
        }
        JTerm t0 = formatArithTerm(tb.not(problem), tb, integerLDT, caches);
        arithTerm =
            tb.geq(tb.func(addfun, t0.sub(0), ab.sub(1)), tb.func(addfun, ab.sub(0), t0.sub(1)));
        res = provedByArith(arithTerm, services);
        if (res.op() == Junctor.TRUE) {
            synchronized (provedByArithCache) {
                provedByArithCache.put(key, falseT);
            }
            return falseT;
        }
        synchronized (provedByArithCache) {
            provedByArithCache.put(key, problem);
        }
        return problem;
    }


    /**
     * Format literal to a form of "geq",linke a>=b;For example, a <=b to b>=a;a>b to a>=b+1;!(a>=b)
     * to b>=a+1..
     *
     * @param problem
     * @return falseT if <code>term</code>'s operator is not >= or <=
     */
    private static JTerm formatArithTerm(final JTerm problem, TermBuilder tb, IntegerLDT ig,
            ServiceCaches caches) {
        final LRUCache<JTerm, JTerm> formattedTermCache = caches.getFormattedTermCache();
        JTerm pro;
        synchronized (formattedTermCache) {
            pro = formattedTermCache.get(problem);
        }
        if (pro != null) {
            return pro;
        }

        pro = problem;
        Operator op = pro.op();
        boolean opNot = false;
        while (op == Junctor.NOT) {
            opNot = !opNot;
            pro = pro.sub(0);
            op = pro.op();
        }
        final Function geq = ig.getGreaterOrEquals();
        final Function leq = ig.getLessOrEquals();
        final JTerm falseT = tb.ff();

        if (op == geq) {
            if (opNot) {
                pro = tb.geq(pro.sub(1), tb.func(ig.getAdd(), pro.sub(0), ig.one()));
            }
        } else {
            if (op == leq) {
                if (opNot) {
                    pro = tb.geq(pro.sub(0), tb.func(ig.getAdd(), pro.sub(1), ig.one()));
                } else {
                    pro = tb.geq(pro.sub(1), pro.sub(0));
                }
            } else {
                pro = falseT;
            }
        }

        putInTermCache(formattedTermCache, problem, pro);
        return pro;
    }

}
