package de.uka.ilkd.key.abstraction.signanalysis;

import java.util.Iterator;

import de.uka.ilkd.key.abstraction.AbstractDomainLattice;

/**
 * TODO: Document.
 * 
 * @author Dominic Scheurer
 */
public class SignAnalysisLattice extends AbstractDomainLattice<SignAnalysisDomainElem, Integer> {

   /**
    * TODO: Document.
    */
   public static final SignAnalysisDomainElem[] ABSTRACT_DOMAIN_ELEMS = {
      Bottom.getInstance(),
      Neg.getInstance(),
      Zero.getInstance(),
      Pos.getInstance(),
      Leq.getInstance(),
      Geq.getInstance(),
      Top.getInstance()
   };
   
   @Override
   public SignAnalysisDomainElem abstractFrom(Integer elem) {
      if (elem == 0) {
         return Zero.getInstance();
      } else if (elem < 0) {
         return Neg.getInstance();
      } else if (elem > 0) {
         return Pos.getInstance();
      } else if (elem <= 0) {
         return Geq.getInstance();
      } else if (elem >= 0) {
         return Leq.getInstance();
      } else {
         return Top.getInstance();
      }
   }

   @Override
   public SignAnalysisDomainElem join(SignAnalysisDomainElem a,
         SignAnalysisDomainElem b) {
      
      if (a.isTop() || b.isTop()) {
         return Top.getInstance();
      }
      
      if (a.isLeq()) {
         if (b.isGeq() || b.isPos()) {
            return Top.getInstance();
         } else {
            return Leq.getInstance();
         }
      }
      
      if (a.isGeq()) {
         if (b.isLeq() || b.isNeg()) {
            return Top.getInstance();
         } else {
            return Geq.getInstance();
         }
      }
      
      if (b.isLeq()) {
         if (a.isGeq() || a.isPos()) {
            return Top.getInstance();
         } else {
            return Leq.getInstance();
         }
      }
      
      if (b.isGeq()) {
         if (a.isLeq() || a.isNeg()) {
            return Top.getInstance();
         } else {
            return Geq.getInstance();
         }
      }
      
      if (a.isNeg()) {
         if (b.isZero()) {
            return Leq.getInstance();
         } else if (b.isPos()) {
            return Top.getInstance();
         } else {
            return Neg.getInstance();
         }
      }
      
      if (a.isZero()) {
         if (b.isNeg()) {
            return Leq.getInstance();
         } else if (b.isPos()) {
            return Geq.getInstance();
         } else {
            return Zero.getInstance();
         }
      }
      
      if (a.isPos()) {
         if (b.isZero()) {
            return Geq.getInstance();
         } else if (b.isNeg()) {
            return Top.getInstance();
         } else {
            return Pos.getInstance();
         }
      }
      
      assert(a.isBottom()) : "Bug in sign lattice implementation.";
      return b;
   }

   @Override
   public Iterator<SignAnalysisDomainElem> iterator() {
      return new Iterator<SignAnalysisDomainElem>() {

         int pos = 0;
         final int size = ABSTRACT_DOMAIN_ELEMS.length;
         
         @Override
         public boolean hasNext() {
            return pos < size - 1;
         }

         @Override
         public SignAnalysisDomainElem next() {
            return ABSTRACT_DOMAIN_ELEMS[pos++];
         }

         @Override
         public void remove() {}
      };
   }

}
