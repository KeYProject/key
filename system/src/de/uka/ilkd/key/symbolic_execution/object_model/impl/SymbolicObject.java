package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;

/**
 * Default implementation of {@link ISymbolicObject}.
 * @author Martin Hentschel
 */
public class SymbolicObject extends AbstractSymbolicAssociationValueContainer implements ISymbolicObject {
   /**
    * The {@link Services} to use.
    */
   private Services services;
   
   /**
    * The name.
    */
   private Term name;

   /**
    * Constructor.
    * @param services The {@link Services} to use.
    * @param name The name.
    */
   public SymbolicObject(Services services, Term name) {
      this.services = services;
      this.name = name;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getName() {
      return name;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getNameString() {
      StringBuffer sb = ProofSaver.printTerm(name, services, true);
      return sb.toString();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Sort getType() {
      return name != null ? name.sort() : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getTypeString() {
      Sort sort = getType();
      return sort != null ? sort.toString() : null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return "Object " + getNameString();
   }
}