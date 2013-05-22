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

import org.eclipse.core.resources.IStorage;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.PlatformObject;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IPersistableElement;
import org.eclipse.ui.IStorageEditorInput;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * This class is used to define an input to display in the editor
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class ProofEditorInput extends PlatformObject implements IStorageEditorInput {
   private IStorage storage;
   
   private Proof proof;
   
   private KeYEnvironment<CustomConsoleUserInterface> environment;
   
   // TODO: Add IMethod
   
   /**
    * Constructor
    * @param storage The storage for this {@link IStorageEditorInput}
    */
   public ProofEditorInput(IStorage storage, Proof proof, KeYEnvironment<CustomConsoleUserInterface> environment){
      this.storage=storage;
      this.proof = proof;
      this.environment = environment;
   }

   /** 
    * {@inheritDoc}
    */
   @Override
   public boolean exists() {
      return true;
   }

   /** 
    * {@inheritDoc}
    */
   @Override
   public ImageDescriptor getImageDescriptor() {
      return null;
   }

   /** 
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return storage.getName();
   }

   /** 
    * {@inheritDoc}
    */
   @Override
   public IPersistableElement getPersistable() {
      return null;
   }

   /** 
    * {@inheritDoc}
    */
   @Override
   public String getToolTipText() {
      return "String-based file: " + storage.getName();
   }

   /** 
    * {@inheritDoc}
    */
   @Override
   public IStorage getStorage() throws CoreException {
      return storage;
   }
   
   /**
    * Gives the {@link Proof} of this {@link ProofEditorInput}.
    * @return The {@link Proof} of this {@link ProofEditorInput}.
    */
   public Proof getProof() {
      return proof;
   }

   /**
    * Gives the {@link KeYEnvironment} of this {@link ProofEditorInput}.
    * @return The {@link KeYEnvironment} of this {@link ProofEditorInput}.
    */
   public KeYEnvironment<CustomConsoleUserInterface> getEnvironment() {
      return environment;
   }
}