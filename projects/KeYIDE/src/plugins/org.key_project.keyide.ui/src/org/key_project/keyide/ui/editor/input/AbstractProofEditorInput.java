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

package org.key_project.keyide.ui.editor.input;

import org.eclipse.core.resources.IStorage;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.PlatformObject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IPersistableElement;
import org.eclipse.ui.IStorageEditorInput;
import org.eclipse.ui.editors.text.TextEditor;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

/**
 * Defines the basic functionality for {@link IEditorInput}s used for the {@link KeYEditor}.
 * @author Martin Hentschel
 */
public abstract class AbstractProofEditorInput extends PlatformObject implements IStorageEditorInput {
   /**
    * The {@link KeYEnvironment} in which the {@link Proof} lives.
    */
   private KeYEnvironment<?> environment;
   
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
    * @param environment The {@link KeYEnvironment} in which the {@link Proof} lives.
    * @param method An optional {@link IMethod} from which the {@link Proof} was started.
    * @param name The name of this editor input.
    */
   public AbstractProofEditorInput(KeYEnvironment<?> environment, 
                                   IMethod method,
                                   String name) {
      this.environment = environment;
      this.method = method;
      this.storage = new TextStorage(StringUtil.EMPTY_STRING, name);
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
    * Gives the {@link KeYEnvironment} of this {@link ProofOblInputEditorInput}.
    * @return The {@link KeYEnvironment} of this {@link ProofOblInputEditorInput}.
    */
   public KeYEnvironment<?> getEnvironment() {
      return environment;
   }
}