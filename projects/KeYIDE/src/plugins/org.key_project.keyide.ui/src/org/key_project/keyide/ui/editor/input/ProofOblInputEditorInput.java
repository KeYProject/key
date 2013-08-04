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
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPersistableElement;
import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.ui.editors.text.TextEditor;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * This class is used to define an input to display in the editor
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class ProofOblInputEditorInput extends PlatformObject implements IStorageEditorInput {
   /**
    * The {@link ProofOblInput} to prove.
    */
   private ProofOblInput problem;
   
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
    * Indicates that this {@link IEditorInput} is already in use by an {@link IEditorPart}.
    */
   private boolean inUse;

   /**
    * Constructor.
    * @param problem The {@link ProofOblInput} to prove.
    * @param environment The {@link KeYEnvironment} in which the {@link Proof} lives.
    * @param method An optional {@link IMethod} from which the {@link Proof} was started.
    */
   public ProofOblInputEditorInput(ProofOblInput problem, 
                           KeYEnvironment<CustomConsoleUserInterface> environment, 
                           IMethod method) {
      Assert.isNotNull(problem);
      Assert.isNotNull(environment);
      this.problem = problem;
      this.environment = environment;
      this.method = method;
      this.storage = new TextStorage(StringUtil.EMPTY_STRING, problem.name());
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
    * Gives the {@link ProofOblInput} of this {@link ProofOblInputEditorInput}.
    * @return The {@link ProofOblInput} of this {@link ProofOblInputEditorInput}.
    */
   public ProofOblInput getProblem() {
      return problem;
   }

   /**
    * Gives the {@link KeYEnvironment} of this {@link ProofOblInputEditorInput}.
    * @return The {@link KeYEnvironment} of this {@link ProofOblInputEditorInput}.
    */
   public KeYEnvironment<CustomConsoleUserInterface> getEnvironment() {
      return environment;
   }

   /**
    * Checks if this {@link IEditorInput} is already in use by an {@link IEditorPart}.
    * @return {@code true} in use, {@code false} not in use.
    */
   public boolean isInUse() {
      return inUse;
   }

   /**
    * Defines if this {@link IEditorInput} is already in use by an {@link IEditorPart}.
    * @param inUse {@code true} in use, {@code false} not in use.
    */
   public void setInUse(boolean inUse) {
      this.inUse = inUse;
   }
}
