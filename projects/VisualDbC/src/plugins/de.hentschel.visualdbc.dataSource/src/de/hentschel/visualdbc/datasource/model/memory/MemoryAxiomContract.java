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

import de.hentschel.visualdbc.datasource.model.IDSAxiom;
import de.hentschel.visualdbc.datasource.model.IDSAxiomContract;
import de.hentschel.visualdbc.datasource.model.IDSOperationContract;
import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Default implementation for an {@link IDSOperationContract} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryAxiomContract extends MemorySpecification implements IDSAxiomContract {
   /**
    * The pre condition.
    */
   private String pre;
   
   /**
    * The depp condition.
    */
   private String dep;
   
   /**
    * The parent.
    */
   private IDSAxiom parent;

   /**
    * Default constructor.
    */
   public MemoryAxiomContract() {
   }

   /**
    * Constructor.
    * @param name The name.
    * @param pre The pre condition.
    * @param dep The dep condition.
    */
   public MemoryAxiomContract(String name, String pre, String dep) {
      setName(name);
      setPre(pre);
      setDep(dep);
   }
   
   /**
    * Sets the pre condition.
    * @param pre The pre condition to set.
    */
   public void setPre(String pre) {
      this.pre = pre;
   }

   /**
    * Sets the dep condition.
    * @param dep The dep condition to set.
    */
   public void setDep(String dep) {
      this.dep = dep;
   }

   /**
    * Sets the parent.
    * @param parent The parent to set.
    */
   public void setParent(IDSAxiom parent) {
      this.parent = parent;
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   public String getPre() throws DSException {
      return pre;
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   public String getDep() throws DSException {
      return dep;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSAxiom getParent() throws DSException {
      return parent;
   }
}