// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

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