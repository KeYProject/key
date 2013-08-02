/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package de.hentschel.visualdbc.datasource.model.memory;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.key_project.util.java.ObjectUtil;

import de.hentschel.visualdbc.datasource.model.IDSAxiom;
import de.hentschel.visualdbc.datasource.model.IDSAxiomContract;
import de.hentschel.visualdbc.datasource.model.IDSType;
import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Default implementation for an {@link IDSAxiom} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryAxiom extends MemorySpecification implements IDSAxiom {
   /**
    * The axiom definition.
    */
   private String definition;
   
   /**
    * The parent.
    */
   private IDSType parent;
   
   /**
    * Contains all axiom contracts.
    */
   private List<IDSAxiomContract> axiomContracts = new LinkedList<IDSAxiomContract>();

   /**
    * Default constructor.
    */
   public MemoryAxiom() {
   }
   
   /**
    * Constructor.
    * @param name The name.
    * @param definition The definition.
    */
   public MemoryAxiom(String name, String definition) {
      setName(name);
      setDefinition(definition);
   }

   /**
    * Sets the parent.
    * @param parent The parent to set.
    */
   public void setParent(IDSType parent) {
      this.parent = parent;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSType getParent() throws DSException {
      return parent;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getDefinition() throws DSException {
      return definition;
   }

   /**
    * Sets the definition.
    * @param definition The definition to set.
    */
   public void setDefinition(String definition) {
      this.definition = definition;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSAxiomContract> getAxiomContracts() throws DSException {
      return axiomContracts;
   }
   
   /**
    * Adds the axiom contract and updates his parent reference.
    * @param ac The axiom contract to add.
    */
   public void addAxiomContract(MemoryAxiomContract ac) {
      axiomContracts.add(ac);
      ac.setParent(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSAxiomContract getAxiomContract(String pre, String dep) throws DSException {
      Iterator<IDSAxiomContract> iter = getAxiomContracts().iterator();
      IDSAxiomContract result = null;
      while(result == null && iter.hasNext()) {
         IDSAxiomContract next = iter.next();
         if (next != null && 
             ObjectUtil.equals(next.getPre(), pre) &&
             ObjectUtil.equals(next.getDep(), dep)) {
            result = next;
         }
      }
      return result;
   }
}