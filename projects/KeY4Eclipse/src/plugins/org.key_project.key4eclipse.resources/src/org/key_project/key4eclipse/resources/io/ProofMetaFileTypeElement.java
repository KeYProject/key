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

package org.key_project.key4eclipse.resources.io;

import java.util.LinkedList;

/**
 * An Object that provides the content of a meta files type.
 * @author Stefan Käsdorf
 */
public class ProofMetaFileTypeElement {
//TODO remove this class an extend the reader.
   private String type;
   private LinkedList<String> subTypes;
   
   public ProofMetaFileTypeElement(String type, LinkedList<String> subTypes){
      this.type = type;
      this.subTypes = subTypes;
   }

   public String getType() {
      return type;
   }

   public LinkedList<String> getSubTypes() {
      return subTypes;
   }
   
}