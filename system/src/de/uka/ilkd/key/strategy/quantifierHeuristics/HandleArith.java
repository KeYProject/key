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

package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.rule.metaconstruct.arith.Polynomial;
import de.uka.ilkd.key.util.LRUCache;
import de.uka.ilkd.key.util.Pair;

/**
 * This class is used to prove some simple arithmetic problem which are 
 * a==b, a>=b, a<=b; Besides it can be used to prove that a>=b or a<=b by 
 * knowing that c>=d or c<=d;
 *   
 */
public class HandleArith {
		
	private HandleArith() {}
    

	
	/**
     * try to prove atom by using polynomial
     * 
     * @param problem
     * @return <code>trueT</code> if if formu is proved to true,
     *         <code>falseT</code> if false, and <code>problem</code> if it
     *         cann't be proved.
     */
    public static Term provedByArith(Term problem, Services services) {
       final LRUCache<Term, Term> provedByArithCache = services.getCaches().getProvedByArithFstCache();
       Term result = provedByArithCache.get(problem);
       if (result != null) {
          return result;
       }
       
       TermBuilder tb = services.getTermBuilder();
       IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
       
       final Term trueT = tb.tt(); 
       final Term falseT = tb.ff(); 

       final Term arithTerm = formatArithTerm ( problem, tb, integerLDT, services.getCaches());
       if ( arithTerm.equals ( falseT ) ) {
          result = provedArithEqual ( problem, tb, services );
          provedByArithCache.put(problem, result);
          return result;
       }
        Polynomial poly1 = Polynomial.create ( arithTerm.sub ( 0 ), services );
        Polynomial poly2 = Polynomial.create ( arithTerm.sub ( 1 ), services );
        if ( poly2.valueLeq ( poly1 ) ) {
            provedByArithCache.put(problem, trueT);
            return trueT;
        }
        if ( poly1.valueLess ( poly2 ) ) {
            provedByArithCache.put(problem, falseT);
            return falseT;
        }
        provedByArithCache.put(problem, problem);
        return problem;
    }
        
    /**
     * @param problem
     * @return true if atom.sub(0) is euqual to atom.sub(1), false if not
     *         equal, else return atom
     */
    private static Term provedArithEqual(Term problem, TermBuilder tb, Services services) {
       final Term trueT = tb.tt(); 
       final Term falseT = tb.ff(); 

        boolean temp = true;
        Term pro = problem;
        Operator op = pro.op ();
        // may be here we should check wehre sub0 and sub1 is integer.
        while ( op == Junctor.NOT ) {
            pro = pro.sub ( 0 );
            op = pro.op ();
            temp = !temp;
        }
        if ( op == Equality.EQUALS ) {
            Term sub0 = pro.sub ( 0 );
            Term sub1 = pro.sub ( 1 );
            Polynomial poly1 = Polynomial.create ( sub0, services );
            Polynomial poly2 = Polynomial.create ( sub1, services );
            boolean gt = poly2.valueLeq ( poly1 );
            boolean lt = poly1.valueLeq ( poly2 );
            if ( gt && lt ) return temp ? trueT : falseT;
            if ( gt || lt ) return temp ? falseT : trueT;
        }
        return problem;
    }
    

    /**
     * Try to prove problem by know that axiom is true. The idea is that we
     * know a>=b(axiom),we want to prove c>=d(problem). It is enough to
     * prove that c+b>=a+d which means c>=d is true. or we prove that
     * !(c>=d) which is d>=c+1 is true. This means c>= d is false;
     * 
     * @param problem
     * @param axiom
     * @return trueT if true, falseT if false, and atom if can't be prove;
     */
    public static Term provedByArith(Term problem, Term axiom, Services services) {
        final Pair<Term, Term> key = new Pair<Term, Term>(problem, axiom);
        final LRUCache<Pair<Term, Term>, Term> provedByArithCache = 
              services.getCaches().getProvedByArithSndCache();
        Term result = provedByArithCache.get(key);
        if (result != null) {
           return result;
        }
       
        final TermBuilder tb = services.getTermBuilder();
        final IntegerLDT integerLDT = services.getTypeConverter ().getIntegerLDT ();
        final ServiceCaches caches = services.getCaches();
        
        final Term cd = formatArithTerm ( problem, tb, integerLDT, caches );
        final Term ab = formatArithTerm ( axiom, tb, integerLDT, caches );
        final Term trueT = tb.tt(); 
        final Term falseT = tb.ff(); 

        if ( cd.op() == Junctor.FALSE || ab.op() == Junctor.FALSE ) {
           provedByArithCache.put(key, problem);
           return problem;
        }
        Function addfun = integerLDT.getAdd();
        Term arithTerm = tb.geq ( tb.func ( addfun, cd.sub ( 0 ), ab.sub ( 1 ) ),
                                  tb.func ( addfun, ab.sub ( 0 ), cd.sub ( 1 ) ) );
        Term res = provedByArith ( arithTerm, services );
        if ( res.op() == Junctor.TRUE ) {
           provedByArithCache.put(key, trueT);
           return trueT;
        }
        Term t0 = formatArithTerm ( tb.not ( problem ), tb, integerLDT, caches );
        arithTerm = tb.geq ( tb.func ( addfun, t0.sub ( 0 ), ab.sub ( 1 ) ),
                             tb.func ( addfun, ab.sub ( 0 ), t0.sub ( 1 ) ) );
        res = provedByArith ( arithTerm, services );
        if ( res.op() == Junctor.TRUE ) {
           provedByArithCache.put(key, falseT);
           return falseT;
        }
        provedByArithCache.put(key, problem);
        return problem;
    }

    
    /**
     * Format literal to a form of "geq",linke a>=b;For example, a <=b to
     * b>=a;a>b to a>=b+1;!(a>=b) to b>=a+1..
     * 
     * @param problem
     * @return falseT if <code>term</code>'s operator is not >= or <=
     */
    private static Term formatArithTerm(final Term problem, TermBuilder tb, IntegerLDT ig, ServiceCaches caches) {
       final LRUCache<Term, Term> formattedTermCache = caches.getFormattedTermCache();
       Term pro = formattedTermCache.get(problem); 
       if (pro != null) {
          return pro;
       }
       
        pro = problem;
        Operator op = pro.op ();
        boolean opNot = false;
        while ( op == Junctor.NOT ) {
            opNot = !opNot;
            pro = pro.sub ( 0 );
            op = pro.op ();
        }
        Function geq = ig.getGreaterOrEquals ();
        Function leq = ig.getLessOrEquals ();
        final Term falseT = tb.ff(); 

        if ( op == geq ) {
            if ( opNot )
                        pro = tb.geq ( pro.sub ( 1 ),
                                       tb.func ( ig.getAdd(),
                                                 pro.sub ( 0 ),
                                                 ig.one() ) );
        } else {
            if ( op == leq ) {
                if ( opNot )
                    pro = tb.geq ( pro.sub ( 0 ),
                                   tb.func ( ig.getAdd (),
                                             pro.sub ( 1 ),
                                             ig.one() ) );
                else
                    pro = tb.geq ( pro.sub ( 1 ), pro.sub ( 0 ) );
            } else
                pro = falseT;
        }
        
        formattedTermCache.put(problem, pro);
        return pro;
    }
    
}