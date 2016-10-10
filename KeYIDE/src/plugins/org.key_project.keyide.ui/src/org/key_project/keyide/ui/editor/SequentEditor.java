package org.key_project.keyide.ui.editor;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.EventObject;

import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.views.properties.IPropertySheetPage;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertySheetPageContributor;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.key_project.key4eclipse.common.ui.decorator.ProofSourceViewerDecorator;
import org.key_project.util.bean.IBean;
import org.key_project.util.java.ArrayUtil;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.control.event.TermLabelVisibilityManagerEvent;
import de.uka.ilkd.key.control.event.TermLabelVisibilityManagerListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SettingsListener;

/**
 * A specialized {@link TextEditor} used to show {@link Sequent}s.
 * @author Martin Hentschel
 */
public class SequentEditor extends TextEditor implements IBean, ITabbedPropertySheetPageContributor, IPosInSequentProvider {
   /**
    * The ID of this {@link ITabbedPropertySheetPageContributor}.
    */
   public static final String CONTRIBUTOR_ID = "org.key_project.keyide.ui.KeYPropertyContributor";
   
   /**
    * The used {@link PropertyChangeSupport}.
    */
   private final PropertyChangeSupport pcs = new PropertyChangeSupport(this);
   
   /**
    * The used {@link ProofSourceViewerDecorator}.
    */
   private ProofSourceViewerDecorator viewerDecorator;


   /**
    * Listens for changes on {@code ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()}.
    */
   private final SettingsListener viewSettingsListener = new SettingsListener() {
      @Override
      public void settingsChanged(EventObject e) {
         handleViewSettingsChanged(e);
      }
   };
   
   /**
    * The currently shown {@link Node}.
    */
   private Node currentNode;
   
   /**
    * The currently used {@link NotationInfo}.
    */
   private NotationInfo currentNotationInfo;
   
   /**
    * The currently used {@link VisibleTermLabels}.
    */
   private VisibleTermLabels currentVisibleLabels;
   
   /**
    * The currently used {@link TermLabelVisibilityManager}.
    */
   private TermLabelVisibilityManager currentTermLabelVisibilityManager;
   
   /**
    * Observes changes on the used {@link TermLabelVisibilityManager}.
    */
   private final TermLabelVisibilityManagerListener termLabelVisibilityManagerListener = new TermLabelVisibilityManagerListener() {
      @Override
      public void visibleLabelsChanged(TermLabelVisibilityManagerEvent e) {
         handleVisibleLabelsChanged(e);
      }
   };

   /**
    * Constructor.
    */
   public SequentEditor() {
      ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().addSettingsListener(viewSettingsListener);
      setEditorContextMenuId("#KeYEditorContext");
      setRulerContextMenuId("#KeYEditorRulerContext"); // Use own ID to disable globale actions like "Add Bookmark" or "Add Task".
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().removeSettingsListener(viewSettingsListener);
      if (currentTermLabelVisibilityManager != null) {
         currentTermLabelVisibilityManager.removeTermLabelVisibilityManagerListener(termLabelVisibilityManagerListener);
      }
      if (viewerDecorator != null) {
         viewerDecorator.dispose();
      }
      super.dispose();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      super.createPartControl(parent);
      ISourceViewer sourceViewer = getSourceViewer();
      viewerDecorator = new ProofSourceViewerDecorator(sourceViewer);
      viewerDecorator.addPropertyChangeListener(ProofSourceViewerDecorator.PROP_SELECTED_POS_IN_SEQUENT, new PropertyChangeListener() {
         @Override
         public void propertyChange(PropertyChangeEvent evt) {
            handleViewerDecoratorSelectedPosInSequentChanged(evt);
         }
      });
      sourceViewer.setEditable(false);
   }
   
   /**
    * When the selected {@link PosInSequent} in {@link #viewerDecorator} has changed.
    * @param evt The event.
    */
   protected void handleViewerDecoratorSelectedPosInSequentChanged(PropertyChangeEvent evt) {
      firePropertyChange(PROP_SELECTED_POS_IN_SEQUENT, evt.getOldValue(), evt.getNewValue());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isEditorInputModifiable() {
      return false; // Text editor is read-only. This disables the replace functionality of the search and replace dialog.
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isEditorInputReadOnly() {
      return true; // Opposite of isEditorInputModifiable()
   }

   /**
    * When the settings of {@code ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()} have changed.
    * @param e The event.
    */
   protected void handleViewSettingsChanged(EventObject e) {
      updateShownSequentThreadSave();
   }

   /**
    * When the visible term labels have changed.
    * @param e The event.
    */
   protected void handleVisibleLabelsChanged(TermLabelVisibilityManagerEvent e) {
      updateShownSequentThreadSave();
   }
   
   /**
    * Updates the shown {@link Sequent} thread save.
    */
   protected void updateShownSequentThreadSave() {
      getSite().getShell().getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            showNode(currentNode, currentNotationInfo, currentVisibleLabels, currentTermLabelVisibilityManager);
         }
      });
   }
   
   /**
    * Shows the given {@link Node} with help of the given {@link KeYMediator}
    * in the decorated {@link ISourceViewer}.
    * @param node The {@link Node} to show.
    * @param notationInfo The {@link NotationInfo} containing information on how to display node.
    * @param visibleLabels The visible term labels.
    * @param termLabelVisibilityManager The {@link TermLabelVisibilityManager} to use.
    */
   public void showNode(Node node, 
                        NotationInfo notationInfo, 
                        VisibleTermLabels visibleLabels, 
                        TermLabelVisibilityManager termLabelVisibilityManager) {
      this.currentNode = node;
      this.currentNotationInfo = notationInfo;
      this.currentVisibleLabels = visibleLabels;
      if (this.currentTermLabelVisibilityManager != null) {
         this.currentTermLabelVisibilityManager.removeTermLabelVisibilityManagerListener(termLabelVisibilityManagerListener);
      }
      this.currentTermLabelVisibilityManager = termLabelVisibilityManager;
      if (this.currentTermLabelVisibilityManager != null) {
         this.currentTermLabelVisibilityManager.addTermLabelVisibilityManagerListener(termLabelVisibilityManagerListener);
      }
      viewerDecorator.showNode(node, notationInfo, visibleLabels);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public PosInSequent getSelectedPosInSequent() {
      return viewerDecorator.getSelectedPosInSequent();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter) {
      if (IPropertySheetPage.class.equals(adapter)) {
         final TabbedPropertySheetPage pcp = new TabbedPropertySheetPage(this);
         // Make sure that initial content is shown even if the focus is set to the outline view and not to the editor. 
         getSite().getShell().getDisplay().asyncExec(new Runnable() {
            @Override
            public void run() {
               if (!pcp.getControl().isDisposed()) {
                  pcp.selectionChanged(SequentEditor.this, getSelectionProvider().getSelection());
               }
            }
         });
         return pcp;
      }
      else {
         return super.getAdapter(adapter);
      }
   }

   /**
    * {@inheritDoc}
    * @return
    */
   @Override
   public String getContributorId() {
      return CONTRIBUTOR_ID;
   }
   
   /**
    * Returns the used {@link PropertyChangeSupport}.
    * @return the used {@link PropertyChangeSupport}.
    */
   protected PropertyChangeSupport getPcs() {
       return pcs;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addPropertyChangeListener(PropertyChangeListener listener) {
       pcs.addPropertyChangeListener(listener);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
       pcs.addPropertyChangeListener(propertyName, listener);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void removePropertyChangeListener(PropertyChangeListener listener) {
       pcs.removePropertyChangeListener(listener);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
       pcs.removePropertyChangeListener(propertyName, listener);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public PropertyChangeListener[] getPropertyChangeListeners() {
       return pcs.getPropertyChangeListeners();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public PropertyChangeListener[] getPropertyChangeListeners(String propertyName) {
       return pcs.getPropertyChangeListeners(propertyName);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasListeners() {
       return getPropertyChangeListeners().length >= 1;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasListeners(String propertyName) {
       return pcs.hasListeners(propertyName);
   }
   
   /**
    * Fires the event to all available listeners.
    * @param propertyName The property name.
    * @param index The changed index.
    * @param oldValue The old value.
    * @param newValue The new value.
    */
   protected void fireIndexedPropertyChange(String propertyName, int index, boolean oldValue, boolean newValue) {
       pcs.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
   }
   
   /**
    * Fires the event to all available listeners.
    * @param propertyName The property name.
    * @param index The changed index.
    * @param oldValue The old value.
    * @param newValue The new value.
    */
   protected void fireIndexedPropertyChange(String propertyName, int index, int oldValue, int newValue) {
       pcs.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
   }
   
   /**
    * Fires the event to all available listeners.
    * @param propertyName The property name.
    * @param index The changed index.
    * @param oldValue The old value.
    * @param newValue The new value.
    */    
   protected void fireIndexedPropertyChange(String propertyName, int index, Object oldValue, Object newValue) {
       pcs.fireIndexedPropertyChange(propertyName, index, oldValue, newValue);
   }
   
   /**
    * Fires the event to all listeners.
    * @param evt The event to fire.
    */
   protected void firePropertyChange(PropertyChangeEvent evt) {
       pcs.firePropertyChange(evt);
   }
   
   /**
    * Fires the event to all listeners.
    * @param propertyName The changed property.
    * @param oldValue The old value.
    * @param newValue The new value.
    */
   protected void firePropertyChange(String propertyName, boolean oldValue, boolean newValue) {
       pcs.firePropertyChange(propertyName, oldValue, newValue);
   }
   
   /**
    * Fires the event to all listeners.
    * @param propertyName The changed property.
    * @param oldValue The old value.
    * @param newValue The new value.
    */
   protected void firePropertyChange(String propertyName, int oldValue, int newValue) {
       pcs.firePropertyChange(propertyName, oldValue, newValue);
   }
   
   /**
    * Fires the event to all listeners.
    * @param propertyName The changed property.
    * @param oldValue The old value.
    * @param newValue The new value.
    */
   protected void firePropertyChange(String propertyName, Object oldValue, Object newValue) {
       pcs.firePropertyChange(propertyName, oldValue, newValue);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasListener(PropertyChangeListener listener) {
       return ArrayUtil.contains(getPropertyChangeListeners(), listener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasListener(String propertyName, PropertyChangeListener listener) {
       return ArrayUtil.contains(getPropertyChangeListeners(propertyName), listener);
   }
}
