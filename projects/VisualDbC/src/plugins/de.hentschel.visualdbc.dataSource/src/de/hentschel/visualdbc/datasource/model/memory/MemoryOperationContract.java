/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
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

import de.hentschel.visualdbc.datasource.model.IDSOperation;
import de.hentschel.visualdbc.datasource.model.IDSOperationContract;
import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Default implementation for an {@link IDSOperationContract} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryOperationContract extends MemorySpecification implements IDSOperationContract {
   /**
    * The pre condition.
    */
   private String pre;
   
   /**
    * The post condition.
    */
   private String post;
   
   /**
    * The modifies.
    */
   private String modifies;
   
   /**
    * The termination.
    */
   private String termination;
   
   /**
    * The parent.
    */
   private IDSOperation parent;

   /**
    * Default constructor.
    */
   public MemoryOperationContract() {
   }

   /**
    * Constructor.
    * @param name The name.
    * @param pre The pre condition.
    * @param post The post condition.
    * @param modifies The modfies.
    * @param termination The termination.
    */
   public MemoryOperationContract(String name, String pre, String post, String modifies, String termination) {
      setName(name);
      setPre(pre);
      setPost(post);
      setModifies(modifies);
      setTermination(termination);
   }
   
   /**
    * Sets the pre condition.
    * @param pre The pre condition to set.
    */
   public void setPre(String pre) {
      this.pre = pre;
   }

   /**
    * Sets the post condition.
    * @param post The post condition to set.
    */
   public void setPost(String post) {
      this.post = post;
   }

   /**
    * Sets the modifies.
    * @param modifies The modifies to set.
    */
   public void setModifies(String modifies) {
      this.modifies = modifies;
   }

   /**
    * Sets the termination.
    * @param termination The termination to set.
    */
   public void setTermination(String termination) {
      this.termination = termination;
   }

   /**
    * Sets the parent.
    * @param parent The parent to set.
    */
   public void setParent(IDSOperation parent) {
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
   public String getPost() throws DSException {
      return post;
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   public String getModifies() throws DSException {
      return modifies;
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   public String getTermination() throws DSException {
      return termination;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSOperation getParent() throws DSException {
      return parent;
   }
}