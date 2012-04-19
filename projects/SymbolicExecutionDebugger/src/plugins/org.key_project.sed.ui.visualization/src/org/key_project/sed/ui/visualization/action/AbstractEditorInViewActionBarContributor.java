package org.key_project.sed.ui.visualization.action;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.gef.ui.actions.ActionBarContributor;
import org.eclipse.jface.action.IAction;
import org.eclipse.ui.IEditorActionBarContributor;
import org.key_project.util.eclipse.view.editorInView.AbstractEditorInViewView;
import org.key_project.util.eclipse.view.editorInView.IGlobalEnablement;

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
   
   // TODO: Wrap registered RetargetAction to keep them enabled if the view part is not active.

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
         GlobalEnablementWrapperAction wrapper = new GlobalEnablementWrapperAction(action); 
         registerGlobalEnablement(wrapper);
         super.addAction(wrapper);
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
}