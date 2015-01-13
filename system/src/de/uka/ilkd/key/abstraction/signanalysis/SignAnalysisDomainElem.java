package de.uka.ilkd.key.abstraction.signanalysis;

import de.uka.ilkd.key.abstraction.AbstractDomainElement;

/**
 * TODO: Document.
 * 
 * @author Dominic Scheurer
 */
public abstract class SignAnalysisDomainElem extends AbstractDomainElement {
   
   public boolean isBottom() {
      return this instanceof Bottom;
   }
   
   public boolean isNeg() {
      return this instanceof Neg;
   }
   
   public boolean isZero() {
      return this instanceof Zero;
   }
   
   public boolean isPos() {
      return this instanceof Pos;
   }
   
   public boolean isLeq() {
      return this instanceof Leq;
   }
   
   public boolean isGeq() {
      return this instanceof Geq;
   }
   
   public boolean isTop() {
      return this instanceof Top;
   }
   
}
