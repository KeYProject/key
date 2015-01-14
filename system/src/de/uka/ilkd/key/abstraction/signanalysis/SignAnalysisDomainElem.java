package de.uka.ilkd.key.abstraction.signanalysis;

import de.uka.ilkd.key.abstraction.AbstractDomainElement;

/**
 * TODO: Document.
 * 
 * @author Dominic Scheurer
 */
public abstract class SignAnalysisDomainElem extends AbstractDomainElement {

   /**
    * @return true iff this element is the neg element.
    */
   public boolean isBottom() {
      return this instanceof Bottom;
   }
   
   /**
    * @return true iff this element is the neg element.
    */
   public boolean isNeg() {
      return this instanceof Neg;
   }
   
   /**
    * @return true iff this element is the zero element.
    */
   public boolean isZero() {
      return this instanceof Zero;
   }

   /**
    * @return true iff this element is the pos element.
    */
   public boolean isPos() {
      return this instanceof Pos;
   }

   /**
    * @return true iff this element is the leq element.
    */
   public boolean isLeq() {
      return this instanceof Leq;
   }

   /**
    * @return true iff this element is the geq element.
    */
   public boolean isGeq() {
      return this instanceof Geq;
   }
   
   /**
    * @return true iff this element is the zero element.
    */
   public boolean isTop() {
      return this instanceof Top;
   }
   
}
