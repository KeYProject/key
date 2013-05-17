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

package org.key_project.keyide.ui.editor.input;

import java.io.InputStream;
import java.io.ByteArrayInputStream;
import org.eclipse.core.resources.IStorage;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.PlatformObject;


/**
 * This class is used to provide non-file input to the editor.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class ProofStorage extends PlatformObject implements IStorage {
   
   private String proofString;
   private String name;
   
   
   /**
    * Constructor.
    * @param input The textbody of this storage
    * @param name The name of this {@link IStorage}.
    */
   public ProofStorage(String input, String name){
      this.proofString=input;
      this.name=name;
   }

   /** 
    * {@inheritDoc}
    */
   @Override
   public InputStream getContents() throws CoreException {
      return new ByteArrayInputStream(proofString.getBytes());
   }

   /** 
    * {@inheritDoc}
    */
   @Override
   public IPath getFullPath() {
      return null;
   }

   /** 
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return name;
   }

   /** 
    * {@inheritDoc}
    */
   @Override
   public boolean isReadOnly() {
      return true;
   }
}