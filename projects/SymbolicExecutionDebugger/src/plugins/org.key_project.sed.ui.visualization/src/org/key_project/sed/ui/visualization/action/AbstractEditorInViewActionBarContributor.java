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

package org.key_project.sed.ui.visualization.action;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.gef.ui.actions.ActionBarContributor;
import org.eclipse.jface.action.IAction;
import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.actions.RetargetAction;
import org.key_project.util.eclipse.view.editorInView.AbstractEditorInViewView;
import org.key_project.util.eclipse.view.editorInView.GlobalEnablementWrapperAction;
import org.key_project.util.eclipse.view.editorInView.IGlobalEnablement;
import org.key_project.util.eclipse.view.editorInView.NoRetargetWrapperRetargetAction;

/**
 * <p>
 * Implementation of {@link ActionBarContributor} which is an {@link IEditorActionBarContributor}
 * for GEF based diagram editors which also realizes the {@link IGlobalEnablement}
 * required for usage in an {@link AbstractEditorInViewView}. Contained actions
 * registered via {@link #addAction(IAction)} are automatically wrapped
 * with a {@link GlobalEnablementWrapperAction} and registered as child
 * {@link IGlobalEnablement} via {@link #registerGlobalEnablement(IGlobalEnablement)}.
 * Contributions which directly instantiates UI controls must be registered
 * via {@link #registerGlobalEnablement(IGlobalEnablement)} to share the global
 * enabled state. 
 * </p>
 * <p>
 * The state of this {@link IGlobalEnablement} is automatically updated by
 * the {@link AbstractEditorInViewView} when the editor becomes visible or 
 * is hidden.
 * </p>
 * @author Martin Hentschel
 * @see AbstractEditorInViewView
 * @see IGlobalEnablement
 * @see ActionBarContributor
 * @see IEditorActionBarContributor
 */
public abstract class AbstractEditorInViewActionBarContributor extends ActionBarContributor implements IGlobalEnablement {
   /**
    * The global enablement state which is shared with child {@link IGlobalEnablement} ({@link #childGlobalEnablements}).
    */
   private boolean globalEnabled;

   /**
    * Contains child {@link IGlobalEnablement} which have always the same global enablement state.
    */
   private List<IGlobalEnablement> childGlobalEnablements = new LinkedList<IGlobalEnablement>();
   
   /**
    * The fixed {@link IWorkbenchPart} which should always be used as source in {@link RetargetAction}s.
    */
   private IWorkbenchPart fixedPart;

   /**
    * Constructor
    * @param fixedPart The fixed {@link IWorkbenchPart} which should always be used as source in {@link RetargetAction}s.
    */
   public AbstractEditorInViewActionBarContributor(IWorkbenchPart fixedPart) {
      super();
      this.fixedPart = fixedPart;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      for (IGlobalEnablement child : childGlobalEnablements) {
         child.dispose();
      }
      childGlobalEnablements.clear();
      super.dispose();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void addAction(IAction action) {
      if (action instanceof IGlobalEnablement) {
         registerGlobalEnablement((IGlobalEnablement)action);
         super.addAction(action);
      }
      else {
         GlobalEnablementWrapperAction wrapper = createActionWrapper(action);
         registerGlobalEnablement(wrapper);
         super.addAction(wrapper);
      }
   }
   
   /**
    * Creates a {@link GlobalEnablementWrapperAction} for the given {@link IAction}.
    * @param action The {@link IAction} to instantiate {@link GlobalEnablementWrapperAction} for.
    * @return The instantiated {@link GlobalEnablementWrapperAction} which wrapps the given {@link IAction}.
    */
   protected GlobalEnablementWrapperAction createActionWrapper(IAction action) {
      return new GlobalEnablementWrapperAction(action);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void addRetargetAction(RetargetAction action) {
      if (action instanceof NoRetargetWrapperRetargetAction) {
         super.addRetargetAction(action);
      }
      else {
         super.addRetargetAction(new NoRetargetWrapperRetargetAction(action, fixedPart));
      }
   }

   /**
    * Registers the new child {@link IGlobalEnablement} in {@link #childGlobalEnablements}
    * and sets the global enablement state on it to the state of this {@link IGlobalEnablement}.
    * @param globalEnablement The child {@link IGlobalEnablement} to register.
    */
   public void registerGlobalEnablement(IGlobalEnablement globalEnablement) {
      childGlobalEnablements.add(globalEnablement);
      globalEnablement.setGlobalEnabled(isGlobalEnabled());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isGlobalEnabled() {
      return globalEnabled;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setGlobalEnabled(boolean globalEnabled) {
      this.globalEnabled = globalEnabled;
      for (IGlobalEnablement child : childGlobalEnablements) {
         child.setGlobalEnabled(globalEnabled);
      }
   }
   
   /**
    * Returns the fixed {@link IWorkbenchPart} which should always be used as source in {@link RetargetAction}s.
    * @return The fixed {@link IWorkbenchPart} which should always be used as source in {@link RetargetAction}s.
    */
   public IWorkbenchPart getFixedPart() {
      return fixedPart;
   }
}