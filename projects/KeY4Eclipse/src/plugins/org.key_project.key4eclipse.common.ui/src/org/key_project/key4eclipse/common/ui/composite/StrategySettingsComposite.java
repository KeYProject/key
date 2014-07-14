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

package org.key_project.key4eclipse.common.ui.composite;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StackLayout;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ScrolledForm;
import org.eclipse.ui.forms.widgets.Section;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;
import org.key_project.key4eclipse.starter.core.util.event.IProofProviderListener;
import org.key_project.key4eclipse.starter.core.util.event.ProofProviderEvent;
import org.key_project.util.eclipse.swt.IntegerVerifyListener;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.XMLUtil;

import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.configuration.SettingsListener;
import de.uka.ilkd.key.gui.configuration.StrategySettings;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.definition.AbstractStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.OneOfStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.StrategyPropertyValueDefinition;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * This {@link Composite} allows to edit the {@link StrategySettings} of
 * the current proof provided by the given {@link IProofProvider} via
 * {@link IProofProvider#getCurrentProof()}.
 * @author Martin Hentschel
 */
public class StrategySettingsComposite extends Composite {
   /**
    * The {@link IProofProvider} which provides the proof to edit its {@link StrategySettings}.
    */
   private IProofProvider proofProvider;
   
   /**
    * Listens for changes of the provided {@link Proof} by {@link #proofProvider}.
    */
   private IProofProviderListener proofProviderListener = new IProofProviderListener() {
      @Override
      public void currentProofsChanged(ProofProviderEvent e) {
         updateShownFormThreadSave();
      }
      
      @Override
      public void currentProofChanged(ProofProviderEvent e) {
         updateShownFormThreadSave();
      }
   };
   
   /**
    * The currently edited {@link Proof}.
    */
   private Proof proof;
   
   /**
    * Listens for changes on the {@link StrategySettings} of {@link #proof}.
    */
   private SettingsListener settingsListener = new SettingsListener() {
      @Override
      public void settingsChanged(GUIEvent e) {
         updateShownFormThreadSave();
      }
   };
   
   /**
    * Maps the strategy name to the {@link ScrolledForm} which is used to edit its settings.
    */
   private Map<Name, ScrolledForm> proofForms = new HashMap<Name, ScrolledForm>();
   
   /**
    * The {@link StackLayout} used in this {@link Composite}.
    */
   private StackLayout layout;
   
   /**
    * A {@link Label} which shows an error message if it is not possible to edit {@link StrategySettings}.
    */
   private Label errorLabel;

   /**
    * The {@link FormData} of the currently shown {@link ScrolledForm}.
    */
   private FormData data;
   
   /**
    * The error message which is shown in {@link #errorLabel} in case that {@link Proof} is provided.
    */
   private String noProofErrorMessage;
   
   /**
    * The {@link KeYMediator} in which the current {@link Proof} lives.
    */
   private KeYMediator mediator;

   /**
    * The {@link AutoModeListener} which observes {@link #mediator}.
    */
   private AutoModeListener autoModeListener = new AutoModeListener() {
      @Override
      public void autoModeStopped(ProofEvent e) {
         setFormEditableThreadSave(true);
      }
      
      @Override
      public void autoModeStarted(ProofEvent e) {
         setFormEditableThreadSave(false);
      }
   };
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param proofProvider The {@link IProofProvider} which provides the {@link Proof} to edit its {@link StrategySettings}.
    */
   public StrategySettingsComposite(Composite parent, IProofProvider proofProvider) {
      this(parent, proofProvider, "No proof selected");
   }

   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param proofProvider The {@link IProofProvider} which provides the {@link Proof} to edit its {@link StrategySettings}.
    * @param noProofErrorMessage The error message to show in case that no {@link Proof} is provided.
    */
   public StrategySettingsComposite(Composite parent, IProofProvider proofProvider, String noProofErrorMessage) {
      super(parent, SWT.NONE);
      this.noProofErrorMessage = noProofErrorMessage;
      this.proofProvider = proofProvider;
      if (proofProvider != null) {
         proofProvider.addProofProviderListener(proofProviderListener);
      }
      
      layout = new StackLayout();
      setLayout(layout);
      errorLabel = new Label(this, SWT.NONE);
      updateShownForm();
   }
   
   /**
    * Updates the shown content thread save by calling
    * {@link #updateShownForm()}.
    */
   protected void updateShownFormThreadSave() {
      getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            updateShownForm();
         }
      });
   }

   /**
    * Updates the shown {@link ScrolledForm} when the provided {@link Proof} 
    * or its strategy has changed.
    */
   protected void updateShownForm() {
      Proof oldProof = proof;
      KeYMediator oldMediator = mediator;
      proof = proofProvider != null ? proofProvider.getCurrentProof() : null;
      mediator = proofProvider != null ? proofProvider.getMediator() : null;
      if (oldProof != proof && oldProof != null && !oldProof.isDisposed()) {
         oldProof.getSettings().getStrategySettings().removeSettingsListener(settingsListener);
      }
      if (oldMediator != mediator && oldMediator != null) {
         oldMediator.removeAutoModeListener(autoModeListener);
      }
      if (proof != null && !proof.isDisposed()) {
         if (oldProof != proof) {
            proof.getSettings().getStrategySettings().addSettingsListener(settingsListener);
         }
         if (oldMediator != mediator && mediator != null) {
            mediator.addAutoModeListener(autoModeListener);
         }
         Name strategyName = proof.getSettings().getStrategySettings().getStrategy();
         Profile profile = proof.getInitConfig().getProfile();
         StrategyFactory factory = strategyName != null ? profile.getStrategyFactory(strategyName) : null;
         if (factory == null) {
            factory = profile.getDefaultStrategyFactory();
         }
         StrategySettingsDefinition model = factory != null ? factory.getSettingsDefinition() : null;
         if (model != null) {
            // Show proof settings
            ScrolledForm form = proofForms.get(strategyName);
            if (form == null) {
               FormToolkit toolkit = new FormToolkit(getDisplay());
               form = toolkit.createScrolledForm(this);
               createContent(toolkit, form, factory, model);
               proofForms.put(strategyName, form);
            }
            data = (FormData)form.getData();
            updateShownContent();
            setFormEditable(mediator == null || !mediator.isInAutoMode());
            layout.topControl = form;
         }
         else {
            // Show no strategy error message
            errorLabel.setText("No (supported) strategy selected");
            layout.topControl = errorLabel;
         }
      }
      else {
         // Show no proof error message
         errorLabel.setText(noProofErrorMessage);
         layout.topControl = errorLabel;
      }
      this.layout();
      updateRestoreDefaultEnabled();
   }

   /**
    * Fills the given {@link ScrolledForm} with content defined by the {@link StrategySettingsDefinition}.
    * @param toolkit The {@link FormToolkit} to use.
    * @param form The {@link ScrolledForm} to fill.
    * @param factory The {@link StrategyFactory} which provides the {@link StrategySettingsDefinition}.
    * @param model The {@link StrategySettingsDefinition} which defines the user interface to create.
    */
   protected void createContent(FormToolkit toolkit, ScrolledForm form, StrategyFactory factory, StrategySettingsDefinition model) {
      FormData data = new FormData(model, factory);
      form.setData(data);
      form.getBody().setLayout(new GridLayout(1, false));
      if (model.isShowMaxRuleApplications()) {
         Section maxStepsSection = toolkit.createSection(form.getBody(), SWT.NONE);
         maxStepsSection.setText(model.getMaxRuleApplicationsLabel());
         maxStepsSection.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         final Text maxStepText = toolkit.createText(maxStepsSection, StringUtil.EMPTY_STRING);
         maxStepsSection.setClient(maxStepText);
         data.setMaxStepText(maxStepText);
         maxStepText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         maxStepText.addVerifyListener(new IntegerVerifyListener(0, Integer.MAX_VALUE, true));
         maxStepText.addModifyListener(new ModifyListener() {
            @Override
            public void modifyText(ModifyEvent e) {
               try {
                  int steps = getStepsFromText(maxStepText);
                  ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(steps);
                  proof.getSettings().getStrategySettings().setMaxSteps(steps);
               }
               catch (Exception exc) {
                  LogUtil.getLogger().openErrorDialog(maxStepText.getShell(), exc);
               }
            }
         });
         maxStepText.setTextLimit(7);
      }
      if (!model.getProperties().isEmpty()) {
         Section propertiesSection = toolkit.createSection(form.getBody(), SWT.NONE);
         propertiesSection.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         propertiesSection.setText(model.getPropertiesTitle());
         Composite propertiesComposite = toolkit.createComposite(propertiesSection);
         propertiesComposite.setLayout(new GridLayout(1, false));
         propertiesComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         propertiesSection.setClient(propertiesComposite);
         for (AbstractStrategyPropertyDefinition property : model.getProperties()) {
            createStrategyProperty(data, toolkit, propertiesComposite, factory, true, property);
         }
      }
      Button defaultButton = toolkit.createButton(form.getBody(), "Restore &Defaults", SWT.PUSH);
      defaultButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            restoreDefaultValues();
         }
      });
      data.setDefaultButton(defaultButton);
   }

   /**
    * Returns the maximal steps defined by the given {@link Text}.
    * @param maxStepText The {@link Text} which defines the maximal steps.
    * @return The maximal steps.
    */
   protected int getStepsFromText(Text maxStepText) {
      String text = maxStepText.getText();
      return !StringUtil.isTrimmedEmpty(text) ? 
             Integer.valueOf(text) : 
             0;
   }

   /**
    * Creates the user interface for the given {@link AbstractStrategyPropertyDefinition}.
    * @param data The {@link FormData} to fill.
    * @param toolkit The {@link FormToolkit} to use.
    * @param parent The parent {@link Composite}.
    * @param factory The {@link StrategyFactory} which provides the {@link AbstractStrategyPropertyDefinition}.
    * @param topLevel Top level property?
    * @param property The {@link AbstractStrategyPropertyDefinition} to create the user interface for.
    */
   protected void createStrategyProperty(FormData data, 
                                         FormToolkit toolkit, 
                                         Composite parent, 
                                         final StrategyFactory factory, 
                                         boolean topLevel, 
                                         AbstractStrategyPropertyDefinition property) {
      // Create property
      if (property instanceof OneOfStrategyPropertyDefinition) {
         final OneOfStrategyPropertyDefinition op = (OneOfStrategyPropertyDefinition)property;
         if (topLevel || op.getValues().isEmpty()) {
            Label label = toolkit.createLabel(parent, op.getName());
            label.setToolTipText(XMLUtil.replaceTags(op.getTooltip(), new XMLUtil.HTMLRendererReplacer()));
         }
         if (!op.getValues().isEmpty()) {
            Composite buttonComposite = toolkit.createComposite(parent);
            buttonComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
            buttonComposite.setLayout(new RowLayout());
            if (!topLevel) {
               toolkit.createLabel(buttonComposite, op.getName());
            }
            for (final StrategyPropertyValueDefinition value : op.getValues()) {
               final Button button = toolkit.createButton(buttonComposite, value.getValue(), SWT.RADIO);
               button.setToolTipText(XMLUtil.replaceTags(value.getTooltip(), new XMLUtil.HTMLRendererReplacer()));
               button.setData(value.getApiValue());
               data.addPropertyButton(button, op.getApiKey());
               button.addSelectionListener(new SelectionAdapter() {
                  @Override
                  public void widgetSelected(SelectionEvent e) {
                     if (button.getSelection()) {
                        updateStrategyProperty(factory, op.getApiKey(), value.getApiValue());
                     }
                  }
               });
            }
         }
      }
      else {
         throw new RuntimeException("Unsupported properts \"" + property + "\".");
      }
      // Create sub properties
      for (AbstractStrategyPropertyDefinition subProperty : property.getSubProperties()) {
         createStrategyProperty(data, toolkit, parent, factory, false, subProperty);
      }
   }
   
   /**
    * Updates the shown content in the {@link ScrolledForm}
    * with help of {@link #data}.
    */
   protected void updateShownContent() {
      if (data.getMaxStepText() != null) {
         String text = Integer.toString(proof.getSettings().getStrategySettings().getMaxSteps());
         if (!ObjectUtil.equals(text, data.getMaxStepText().getText())) {
            data.getMaxStepText().setText(text);
         }
      }
      StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
      for (Entry<String, List<Button>> entry : data.getPropertyButtons().entrySet()) {
         String value = sp.getProperty(entry.getKey());
         for (Button button : entry.getValue()) {
            button.setSelection(ObjectUtil.equals(button.getData(), value));
         }
      }
      updateRestoreDefaultEnabled();
   }
   
   /**
    * This method to update a property in the {@link StrategyProperties} when
    * the user selects a new value.
    * @param factory The {@link StrategyFactory}.
    * @param key The key of the property.
    * @param value The value of the property to set.
    */
   protected void updateStrategyProperty(StrategyFactory factory, String key, String value) {
      StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
      sp.setProperty(key, value);
      SymbolicExecutionUtil.updateStrategySettings(proof, sp);
      Strategy strategy = factory.create(proof, sp);
      proof.setActiveStrategy(strategy);
   }
   
   /**
    * Makes the current {@link ScrolledForm} editable or read-only
    * thread save by calling {@link #setFormEditable(boolean)}.
    * @param editable {@code true} editable, {@code false} read-only.
    */
   protected void setFormEditableThreadSave(final boolean editable) {
      getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            setFormEditable(editable);
         }
      });
   }
   
   /**
    * Makes the current {@link ScrolledForm} with help of {@link #data} editable
    * or read-only.
    * @param editable editable {@code true} editable, {@code false} read-only.
    */
   protected void setFormEditable(boolean editable) {
      if (data.getMaxStepText() != null) {
         data.getMaxStepText().setEditable(editable);
      }
      for (Entry<String, List<Button>> entry : data.getPropertyButtons().entrySet()) {
         for (Button button : entry.getValue()) {
            button.setEnabled(editable);
         }
      }
   }
   
   /**
    * Updates the enabled state of the restore default values {@link Button}.
    */
   protected void updateRestoreDefaultEnabled() {
      if (proof != null && !proof.isDisposed() && data != null && data.getDefaultButton() != null) {
         boolean defaultMaxRules = data.getMaxStepText() == null ||
                                   getStepsFromText(data.getMaxStepText()) == data.getModel().getDefaultMaxRuleApplications();
         boolean defaultProperties = proof.getSettings().getStrategySettings().getActiveStrategyProperties().equals(data.getModel().getDefaultPropertiesFactory().createDefaultStrategyProperties());
         data.getDefaultButton().setEnabled(!defaultMaxRules || !defaultProperties);
      }
   }
   
   /**
    * Restores the default values.
    */
   protected void restoreDefaultValues() {
      if (proof != null && data != null) {
         ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setMaxSteps(data.getModel().getDefaultMaxRuleApplications());
         proof.getSettings().getStrategySettings().setMaxSteps(data.getModel().getDefaultMaxRuleApplications());
         StrategyProperties sp = data.getModel().getDefaultPropertiesFactory().createDefaultStrategyProperties();
         SymbolicExecutionUtil.updateStrategySettings(proof, sp);
         Strategy strategy = data.getFactory().create(proof, sp);
         proof.setActiveStrategy(strategy);
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (proofProvider != null) {
         proofProvider.removeProofProviderListener(proofProviderListener);
      }
      if (mediator != null) {
         mediator.removeAutoModeListener(autoModeListener);
      }
      if (proof != null && !proof.isDisposed()) {
         proof.getSettings().getStrategySettings().removeSettingsListener(settingsListener);
      }
      for (ScrolledForm form : proofForms.values()) {
         form.dispose();
      }
      proofForms.clear();
      super.dispose();
   }
   
   /**
    * Provided via {@link ScrolledForm#getData()} for direct access
    * to created user interface components.
    * @author Martin Hentschel
    */
   protected static class FormData {
      /**
       * The {@link StrategySettingsDefinition} from which contained UI controls are created.
       */
      private final StrategySettingsDefinition model;
      
      /**
       * The {@link StrategyFactory} which provides {@link #model}.
       */
      private final StrategyFactory factory;
      
      /**
       * The {@link Text} in which the maximal number of steps is edited.
       */
      private Text maxStepText;
      
      /**
       * Maps a property key to the {@link Button}s which defines the values.
       */
      private Map<String, List<Button>> propertyButtons = new HashMap<String, List<Button>>();
      
      /**
       * The default {@link Button}.
       */
      private Button defaultButton;

      /**
       * Constructor. 
       * @param model The {@link StrategySettingsDefinition} from which contained UI controls are created.
       * @param factory The {@link StrategyFactory} which provides the given {@link StrategySettingsDefinition}.
       */
      public FormData(StrategySettingsDefinition model, StrategyFactory factory) {
         this.model = model;
         this.factory = factory;
      }

      /**
       * Returns the {@link Text} in which the maximal number of steps is edited.
       * @return The {@link Text} in which the maximal number of steps is edited.
       */
      public Text getMaxStepText() {
         return maxStepText;
      }

      /**
       * Sets the {@link Text} in which the maximal number of steps is edited.
       * @param maxStepText The {@link Text} in which the maximal number of steps is edited.
       */
      public void setMaxStepText(Text maxStepText) {
         this.maxStepText = maxStepText;
      }
      
      /**
       * Registers the given {@link Button} for the given key.
       * @param button The {@link Button}.
       * @param key The key.
       */
      public void addPropertyButton(Button button, String key) {
         List<Button> buttons = propertyButtons.get(key);
         if (buttons == null) {
            buttons = new LinkedList<Button>();
            propertyButtons.put(key, buttons);
         }
         buttons.add(button);
      }

      /**
       * Returns the mapping of property keys to the {@link Button}s which defines the values.
       * @return The mapping of property keys to the {@link Button}s which defines the values.
       */
      public Map<String, List<Button>> getPropertyButtons() {
         return propertyButtons;
      }

      /**
       * Returns the default {@link Button}.
       * @return The default {@link Button}.
       */
      public Button getDefaultButton() {
         return defaultButton;
      }

      /**
       * Sets the default {@link Button}.
       * @param defaultButton The default {@link Button} to set.
       */
      public void setDefaultButton(Button defaultButton) {
         this.defaultButton = defaultButton;
      }

      /**
       * Returns the {@link StrategySettingsDefinition} from which contained UI controls are created.
       * @return The {@link StrategySettingsDefinition} from which contained UI controls are created.
       */
      public StrategySettingsDefinition getModel() {
         return model;
      }

      /**
       * Returns the {@link StrategyFactory} which provides {@link #getModel()}.
       * @return The {@link StrategyFactory} which provides {@link #getModel()}.
       */
      public StrategyFactory getFactory() {
         return factory;
      }
   }
}