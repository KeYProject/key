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
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.PlatformObject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IPersistableElement;
import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.ui.editors.text.TextEditor;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * This class is used to define an input to display in the editor
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class ProofEditorInput extends PlatformObject implements IStorageEditorInput {
   /**
    * The {@link Proof}.
    */
   private Proof proof;
   
   /**
    * The {@link KeYEnvironment} in which the {@link Proof} lives.
    */
   private KeYEnvironment<CustomConsoleUserInterface> environment;
   
   /**
    * The optional {@link IMethod} from which the proof was started.
    */
   private IMethod method;

   /**
    * The {@link IStorage} which is used by {@link TextEditor}s to show the initial content
    * which is always an empty string because the {@link KeYEditor} computes it based
    * on the selected {@link Node} itself.
    */
   private IStorage storage;

   /**
    * Constructor.
    * @param proof The {@link Proof}.
    * @param environment The {@link KeYEnvironment} in which the {@link Proof} lives.
    * @param method An optional {@link IMethod} from which the {@link Proof} was started.
    */
   public ProofEditorInput(Proof proof, 
                           KeYEnvironment<CustomConsoleUserInterface> environment, 
                           IMethod method) {
      Assert.isNotNull(proof);
      Assert.isNotNull(environment);
      this.proof = proof;
      this.environment = environment;
      this.method = method;
      this.storage = new TextStorage(StringUtil.EMPTY_STRING, proof.name().toString());
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
    * Returns the optional {@link IMethod} from which the proof was started.
    * @return The optional {@link IMethod} from which the proof was started.
    */
   public IMethod getMethod(){
      return method;
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
