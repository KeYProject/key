package org.key_project.sed.ui.visualization.action;

import org.eclipse.gef.editparts.ZoomManager;
import org.eclipse.gef.ui.actions.ZoomComboContributionItem;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IPartService;
import org.key_project.util.eclipse.view.editorInView.IGlobalEnablement;

/**
 * Special implementation of {@link ZoomComboContributionItem} which
 * has also a global enabled state defined via {@link IGlobalEnablement}.
 * @author Martin Hentschel
 */
public class GlobalEnablementZoomComboContributionItem extends ZoomComboContributionItem implements IGlobalEnablement {
   /**
    * The global enabled state.
    */
   private boolean globalEnabled;
   
   /**
    * The contributed UI control.
    */
   private Control control;
   
   /**
    * Constructor for ComboToolItem.
    * @param partService used to add a PartListener
    * @param initString the initial string displayed in the combo
    */   
   public GlobalEnablementZoomComboContributionItem(IPartService partService, String initString) {
      super(partService, initString);
   }

   /**
    * Constructor for ComboToolItem.
    * @param partService used to add a PartListener
    * @param initStrings the initial string displayed in the combo
    */   
   public GlobalEnablementZoomComboContributionItem(IPartService partService, String[] initStrings) {
      super(partService, initStrings);
   }

   /**
    * Constructor for ComboToolItem.
    * @param partService used to add a PartListener
    */   
   public GlobalEnablementZoomComboContributionItem(IPartService partService) {
      super(partService);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isEnabled() {
      return super.isEnabled() && isGlobalEnabled();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Control createControl(Composite parent) {
      Control result = super.createControl(parent);
      this.control = result;
      updateEnablement();
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void zoomChanged(double zoom) {
      super.zoomChanged(zoom);
      updateEnablement();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setZoomManager(ZoomManager zm) {
      super.setZoomManager(zm);
      updateEnablement();
   }
   
   /**
    * Updates the enabled state of the contributed UI control ({@link #control}).
    */
   protected void updateEnablement() {
      if (this.control != null && !this.control.isDisposed()) {
         this.control.setEnabled(isEnabled());
      }
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
      updateEnablement();
   }
}
