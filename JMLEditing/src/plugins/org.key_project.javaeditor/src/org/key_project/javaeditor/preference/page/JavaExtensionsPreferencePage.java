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

package org.key_project.javaeditor.preference.page;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;

import org.eclipse.jface.preference.IPreferencePageContainer;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.jface.viewers.ICheckStateProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Table;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;
import org.key_project.javaeditor.util.ExtendableConfigurationUtil;
import org.key_project.javaeditor.util.ExtendableConfigurationUtil.ExtensionDescription;
import org.key_project.javaeditor.util.PreferenceUtil;
import org.key_project.util.bean.Bean;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * Preference page for the Java extensions.
 * @author Martin Hentschel
 */
public class JavaExtensionsPreferencePage extends PreferencePage implements IWorkbenchPreferencePage {
   /**
    * The used {@link EnabledState}.
    */
   private EnabledState enabledState;
   
   /**
    * Listens for changes of {@link #enabledState}.
    */
   private final PropertyChangeListener enabledStateListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleEnabledPropertyChange(evt);
      }
   };
   
   /**
    * Checkbox to edit {@link #enabledState}.
    */
   private Button enabledButton;
   
   /**
    * The currently available {@link EnabledState}s.
    */
   private static final WeakHashMap<IPreferencePageContainer, EnabledState> enabledMap = new WeakHashMap<IPreferencePageContainer, EnabledState>();
   
   /**
    * The available {@link ExtensionDescriptionState}s.
    */
   private final List<ExtensionDescriptionState> extensionDescriptionStates = new LinkedList<ExtensionDescriptionState>();
   
   /**
    * Listens for changes on an {@link ExtensionDescriptionState} of {@link #extensionDescriptionStates}.
    */
   private final PropertyChangeListener descriptionStateListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handleDescriptionPropertyChange(evt);
      }
   };

   /**
    * The {@link CheckboxTableViewer} which shows {@link #extensionDescriptionStates}.
    */
   private CheckboxTableViewer extensionsViewer;

   /**
    * Allows access to the currently available {@link ExtensionDescriptionState}s.
    */
   private static final WeakHashMap<IPreferencePageContainer, Map<ExtensionDescription, ExtensionDescriptionState>> stateMaps = new WeakHashMap<IPreferencePageContainer, Map<ExtensionDescription, ExtensionDescriptionState>>();
   
   /**
    * Constructor
    */
   public JavaExtensionsPreferencePage() {
      setPreferenceStore(PreferenceUtil.getStore());
   }

   /**
    * Returns the {@link EnabledState} of the given {@link IPreferencePageContainer}.
    * @param container The {@link IPreferencePageContainer}.
    * @param stateListener The {@link PropertyChangeListener} to add.
    * @return The {@link EnabledState} of the given {@link IPreferencePageContainer}.
    */
   public static EnabledState useEnabledSate(IPreferencePageContainer container,
                                             PropertyChangeListener stateListener) {
      assert container != null;
      assert stateListener != null;
      EnabledState state = enabledMap.get(container);
      if (state == null) {
         state = new EnabledState();
         enabledMap.put(container, state);
      }
      state.addPropertyChangeListener(ExtensionDescriptionState.PROP_CHECKED, stateListener);
      return state;
   }
   
   /**
    * Frees the use of the given {@link EnabledState}.
    * @param state The {@link EnabledState} to free.
    * @param container The used {@link IPreferencePageContainer}.
    * @param stateListener The {@link PropertyChangeListener} to remove.
    */
   public static void freeEnabledState(EnabledState state,
                                       IPreferencePageContainer container,
                                       PropertyChangeListener stateListener) {
      if (state != null) {
         state.removePropertyChangeListener(ExtensionDescriptionState.PROP_CHECKED, stateListener);
         if (ArrayUtil.isEmpty(state.getPropertyChangeListeners(ExtensionDescriptionState.PROP_CHECKED))) {
            enabledMap.remove(container);
         }
      }
   }
   
   /**
    * Returns the {@link ExtensionDescriptionState} to use representing the
    * given {@link ExtensionDescription}. 
    * @param description The {@link ExtensionDescription} of interest.
    * @param container The {@link IPreferencePageContainer} to use.
    * @param stateListener The {@link PropertyChangeListener} to add.
    * @return The {@link ExtensionDescriptionState} representing the given {@link ExtensionDescription}.
    */
   public static ExtensionDescriptionState useState(ExtensionDescription description, 
                                                    IPreferencePageContainer container,
                                                    PropertyChangeListener stateListener) {
      if (description != null) {
         assert container != null;
         assert stateListener != null;
         Map<ExtensionDescription, ExtensionDescriptionState> map = stateMaps.get(container);
         if (map == null) {
            map = new HashMap<ExtensionDescription, ExtensionDescriptionState>();
            stateMaps.put(container, map);
         }
         ExtensionDescriptionState state = map.get(description);
         if (state == null) {
            state = new ExtensionDescriptionState(description);
            map.put(description, state);
         }
         state.addPropertyChangeListener(ExtensionDescriptionState.PROP_CHECKED, stateListener);
         return state;
      }
      else {
         return null;
      }
   }
   
   /**
    * Frees the use of the given {@link ExtensionDescriptionState}.
    * @param state The {@link ExtensionDescriptionState} to free.
    * @param container The used {@link IPreferencePageContainer}.
    * @param stateListener The {@link PropertyChangeListener} to remove.
    */
   public static void freeState(ExtensionDescriptionState state, 
                                IPreferencePageContainer container, 
                                PropertyChangeListener stateListener) {
      if (state != null) {
         assert container != null;
         assert stateListener != null;
         state.removePropertyChangeListener(ExtensionDescriptionState.PROP_CHECKED, stateListener);
         if (ArrayUtil.isEmpty(state.getPropertyChangeListeners(ExtensionDescriptionState.PROP_CHECKED))) {
            Map<ExtensionDescription, ExtensionDescriptionState> map = stateMaps.get(container);
            if (map != null) {
               map.remove(state.getExtensionDescription());
               if (map.isEmpty()) {
                  stateMaps.remove(container);
               }
            }
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      freeEnabledState(enabledState, getContainer(), enabledStateListener);
      for (ExtensionDescriptionState state : extensionDescriptionStates) {
         freeState(state, getContainer(), descriptionStateListener);
      }
      super.dispose();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IWorkbench workbench) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Control createContents(Composite parent) {
      Composite root = new Composite(parent, SWT.NONE);
      root.setLayout(new GridLayout(1, false));
      // Enabled state and control
      enabledState = useEnabledSate(getContainer(), enabledStateListener);
      enabledButton = new Button(root, SWT.CHECK);
      enabledButton.setText("Extensions &Enabled");
      enabledButton.setSelection(enabledState.isChecked());
      enabledButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            handleEnabledSelectionChanged(e);
         }
      });
      // Manage states
      ExtensionDescription[] descriptions = ExtendableConfigurationUtil.getExtensionDescriptions();
      for (ExtensionDescription description : descriptions) {
         ExtensionDescriptionState state = useState(description, getContainer(), descriptionStateListener);
         extensionDescriptionStates.add(state);
      }
      // Create table
      Group extensionsGroup = new Group(root, SWT.NONE);
      extensionsGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
      extensionsGroup.setText("Available Extensions");
      extensionsGroup.setLayout(new GridLayout(1, false));
      extensionsViewer = new CheckboxTableViewer(new Table(extensionsGroup, SWT.BORDER | SWT.SINGLE | SWT.CHECK));
      extensionsViewer.getControl().setLayoutData(new GridData(GridData.FILL_BOTH));
      extensionsViewer.setContentProvider(ArrayContentProvider.getInstance());
      extensionsViewer.setLabelProvider(new LabelProvider() {
         @Override
         public String getText(Object element) {
            if (element instanceof ExtensionDescriptionState) {
               return ((ExtensionDescriptionState) element).getName();
            }
            else {
               return ObjectUtil.toString(element);
            }
         }
      });
      extensionsViewer.setCheckStateProvider(new ICheckStateProvider() {
         @Override
         public boolean isGrayed(Object element) {
            return false;
         }
         
         @Override
         public boolean isChecked(Object element) {
            if (element instanceof ExtensionDescriptionState) {
               return ((ExtensionDescriptionState) element).isChecked();
            }
            else {
               return false;
            }
         }
      });
      extensionsViewer.addCheckStateListener(new ICheckStateListener() {
         @Override
         public void checkStateChanged(CheckStateChangedEvent event) {
            handleCheckStateChanged(event);
         }
      });
      extensionsViewer.setInput(extensionDescriptionStates);
      updateExntesionViewerEnabled();
      return root;
   }

   /**
    * When the selection of {@link #enabledButton} has changed.
    * @param e The {@link SelectionEvent}.
    */
   protected void handleEnabledSelectionChanged(SelectionEvent e) {
      updateExntesionViewerEnabled();
      enabledState.setChecked(enabledButton.getSelection());
   }
   
   /**
    * Updates the enabled state of {@link #extensionsViewer}.
    */
   protected void updateExntesionViewerEnabled() {
      extensionsViewer.getControl().setEnabled(enabledButton.getSelection());
   }

   /**
    * When the checked sate of {@link #enabledState} has changed.
    * @param evt The {@link PropertyChangeEvent}.
    */
   protected void handleEnabledPropertyChange(PropertyChangeEvent evt) {
      enabledButton.setSelection(enabledState.isChecked());
      updateExntesionViewerEnabled();
   }

   /**
    * When the checked state in {@link #extensionsViewer} has changed.
    * @param event The {@link CheckStateChangedEvent}.
    */
   protected void handleCheckStateChanged(CheckStateChangedEvent event) {
      ExtensionDescriptionState state = (ExtensionDescriptionState) event.getElement();
      state.setChecked(event.getChecked());
   }

   /**
    * When the checked state of an {@link ExtensionDescriptionState} of {@link #extensionDescriptionStates} has changed.
    * @param evt The {@link PropertyChangeEvent}.
    */
   protected void handleDescriptionPropertyChange(PropertyChangeEvent evt) {
      ExtensionDescriptionState state = (ExtensionDescriptionState) evt.getSource();
      extensionsViewer.setChecked(state, state.isChecked());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void performDefaults() {
      super.performDefaults();
      enabledState.setChecked(PreferenceUtil.isDefaultExtensionsEnabled());
      for (ExtensionDescriptionState state : extensionDescriptionStates) {
         state.setChecked(PreferenceUtil.isDefaultExtensionEnabled(state.getId()));
      }
      updateExntesionViewerEnabled();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performOk() {
      boolean done = super.performOk();
      PreferenceUtil.setExtensionsEnabled(enabledState.isChecked());
      for (ExtensionDescriptionState state : extensionDescriptionStates) {
         PreferenceUtil.setExtensionEnabled(state.getId(), state.isChecked());
      }
      return done;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void performApply() {
      super.performApply();
      PreferenceUtil.setExtensionsEnabled(enabledState.isChecked());
      for (ExtensionDescriptionState description : extensionDescriptionStates) {
         PreferenceUtil.setExtensionEnabled(description.getId(), extensionsViewer.getChecked(description));
      }
   }
   
   /**
    * The enabled state as shown/edited by this {@link JavaExtensionsPreferencePage}.
    * @author Martin Hentschel
    */
   public static final class EnabledState extends Bean {
      /**
       * Property {@link #isChecked()}.
       */
      public static final String PROP_CHECKED = "checked";
      
      /**
       * The checked state.
       */
      private boolean checked;
      
      /**
       * Constructor.
       */
      private EnabledState() {
         checked = PreferenceUtil.isExtensionsEnabled();
      }

      /**
       * Returns the current checked state.
       * @return The current checked state.
       */
      public boolean isChecked() {
         return checked;
      }

      /**
       * Sets the checked state.
       * @param checked The new checked state to set.
       */
      public void setChecked(boolean checked) {
         boolean oldValue = isChecked();
         this.checked = checked;
         firePropertyChange(PROP_CHECKED, oldValue, isChecked());
      }
   }
   
   /**
    * An instance of this class provides the checked state of an
    * {@link ExtensionDescription} as shown/editied by this {@link JavaExtensionsPreferencePage}.
    * @author Martin Hentschel
    */
   public static final class ExtensionDescriptionState extends Bean {
      /**
       * Property {@link #isChecked()}.
       */
      public static final String PROP_CHECKED = "checked";
      
      /**
       * The {@link ExtensionDescription}.
       */
      private final ExtensionDescription extensionDescription;
      
      /**
       * The checked state.
       */
      private boolean checked;

      /**
       * Constructor.
       * @param extensionDescription The {@link ExtensionDescription}.
       */
      private ExtensionDescriptionState(ExtensionDescription extensionDescription) {
         assert extensionDescription != null;
         this.extensionDescription = extensionDescription;
         this.checked = PreferenceUtil.isExtensionEnabled(extensionDescription.getId());
      }

      /**
       * Returns the {@link ExtensionDescription}.
       * @return The {@link ExtensionDescription}.
       */
      public ExtensionDescription getExtensionDescription() {
         return extensionDescription;
      }

      /**
       * Returns the ID of the {@link ExtensionDescription}.
       * @return The ID of the {@link ExtensionDescription}.
       */
      public String getId() {
         return extensionDescription.getId();
      }

      /**
       * Returns the name of the {@link ExtensionDescription}.
       * @return The name of the {@link ExtensionDescription}.
       */
      public String getName() {
         return extensionDescription.getName();
      }

      /**
       * Returns the current checked state.
       * @return The current checked state.
       */
      public boolean isChecked() {
         return checked;
      }

      /**
       * Sets the checked state.
       * @param checked The new checked state to set.
       */
      public void setChecked(boolean checked) {
         boolean oldValue = isChecked();
         this.checked = checked;
         firePropertyChange(PROP_CHECKED, oldValue, isChecked());
      }
   }
}