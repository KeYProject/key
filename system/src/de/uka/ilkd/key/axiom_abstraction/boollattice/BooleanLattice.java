package de.uka.ilkd.key.axiom_abstraction.boollattice;

import java.util.Iterator;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.AbstractDomainLattice;

/**
 * A simple lattice for booleans.
 * 
 * @author Dominic Scheurer
 */
public class BooleanLattice extends AbstractDomainLattice<Boolean> {
   
   /**
    * All elements of this abstract domain.
    */
   public static final AbstractDomainElement[] ABSTRACT_DOMAIN_ELEMS = {
      Bottom.getInstance(),
      False.getInstance(),
      True.getInstance(),
      Top.getInstance()
   };
   
   /**
    * The singleton instance of the lattice.
    */
   private static final BooleanLattice INSTANCE = new BooleanLattice();
   
   /**
    * Private constructor: Singleton.
    */
   private BooleanLattice() {}
   
   /**
    * @return The singleton instance of this lattice.
    */
   public static BooleanLattice getInstance() {
      return INSTANCE;
   }
   
   @Override
   public AbstractDomainElement abstractFrom(Boolean elem) {
      if (elem) {
         return True.getInstance();
      } else {
         return False.getInstance();
      }
   }

   @Override
   public AbstractDomainElement join(AbstractDomainElement elem1,
         AbstractDomainElement elem2) {
      
      if (!(elem1 instanceof BooleanDomainElem) ||
          !(elem2 instanceof BooleanDomainElem)) {
         throw new IllegalArgumentException("Expected arguments of the abstract domain of sign analysis.");
      }
      
      BooleanDomainElem a = (BooleanDomainElem) elem1;
      BooleanDomainElem b = (BooleanDomainElem) elem2;
      
      if (a.isTop() || b.isTop()) {
         return Top.getInstance();
      }
      
      if (a.isTrue()) {
         if (b.isFalse()) {
            return Top.getInstance();
         } else {
            return True.getInstance();
         }
      }
      
      if (a.isFalse()) {
         if (b.isTrue()) {
            return Top.getInstance();
         } else {
            return False.getInstance();
         }
      }
      
      assert(a.isBottom()) : "Bug in boolean lattice implementation.";
      return b;
   }

   @Override
   public Iterator<AbstractDomainElement> iterator() {
      return new Iterator<AbstractDomainElement>() {

         int pos = 0;
         final int size = ABSTRACT_DOMAIN_ELEMS.length;
         
         @Override
         public boolean hasNext() {
            return pos < size - 1;
         }

         @Override
         public AbstractDomainElement next() {
            return ABSTRACT_DOMAIN_ELEMS[pos++];
         }

         @Override
         public void remove() {}
      };
   }
   
}
