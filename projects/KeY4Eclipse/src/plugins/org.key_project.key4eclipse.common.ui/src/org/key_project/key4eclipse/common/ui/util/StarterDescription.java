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

package org.key_project.key4eclipse.common.ui.util;

import org.eclipse.core.runtime.Assert;

/**
 * Contains the defined values of an extension point which is used
 * to register starters.
 * @author Martin Hentschel
 */
public class StarterDescription<I> {
   /**
    * The unique ID.
    */
   private String id;
   
   /**
    * The human readable name.
    */
   private String name;
   
   /**
    * The instance.
    */
   private I instance;
   
   /**
    * An optional human readable description.
    */
   private String description;

   /**
    * Constructor.
    * @param id The unique ID.
    * @param name The human readable name.
    * @param instance The instance.
    * @param description An optional human readable description.
    */
   public StarterDescription(String id, String name, I instance, String description) {
      Assert.isNotNull(id);
      Assert.isNotNull(name);
      Assert.isNotNull(instance);
      this.id = id;
      this.name = name;
      this.instance = instance;
      this.description = description;
   }

   /**
    * Returns the unique ID.
    * @return The unique ID.
    */
   public String getId() {
      return id;
   }

   /**
    * Returns the human readable name.
    * @return The human readable name.
    */
   public String getName() {
      return name;
   }

   /**
    * Returns the instance.
    * @return The instance.
    */
   public I getInstance() {
      return instance;
   }

   /**
    * Returns the optional human readable description.
    * @return The optional human readable description.
    */
   public String getDescription() {
      return description;
   }
}