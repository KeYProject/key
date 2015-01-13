package de.uka.ilkd.key.abstraction;

import java.util.Iterator;

/**
 * TODO: Document.
 * 
 * @author Dominic Scheurer
 *
 * @param <AbstrDomElem>
 * @param <ConcrDomElem>
 */
public abstract class AbstractDomainLattice<AbstrDomElem extends AbstractDomainElement, ConcrDomElem>
implements PartialComparator<AbstrDomElem>, Iterable<AbstrDomElem> {
   
   /**
    * TODO: Document.
    * 
    * @param elem
    * @return
    */
   public abstract AbstrDomElem abstractFrom(ConcrDomElem elem);
   
   /**
    * TODO: Document.
    * 
    * @param a
    * @param b
    * @return
    */
   public abstract AbstrDomElem join(AbstrDomElem a, AbstrDomElem b);
   
   @Override
   public PartialComparisonResult compare(AbstrDomElem a, AbstrDomElem b) {
      if (a.equals(b)) {
         return PartialComparisonResult.EQ;
      }
      
      AbstrDomElem joinRes = join(a, b);
      if (joinRes.equals(a)) {
         return PartialComparisonResult.GTE;
      } else if (joinRes.equals(b)) {
         return PartialComparisonResult.LTE;
      } else {
         return PartialComparisonResult.UNDEF;
      }
      
   }
   
   /**
    * Iterates through the abstract domain elements of this
    * abstract domain starting by the smallest element; if
    * an element b is returned by the iterator after an element
    * a, the either compare(a,b) == LTE, or compare(a,b) == UNDEF
    * must hold (i.e., b may not be smaller than a). 
    */
   @Override
   public abstract Iterator<AbstrDomElem> iterator();
   
}
