// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.gui;

import java.awt.Component;
import java.awt.Dimension;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.ButtonGroup;
import javax.swing.ButtonModel;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JScrollPane;
import javax.swing.ScrollPaneConstants;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.definition.AbstractStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.OneOfStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.StrategyPropertyValueDefinition;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;

/**
 * <p>
 * This {@link JPanel} allows to edit the {@link StrategyProperties}
 * of the {@link JavaCardDLStrategy}. The shown UI controls are generated
 * according to its {@link StrategySettingsDefinition}.
 * </p>
 * <p>
 * <b>There is no need to change this class to change the available settings!</b>
 * The only thing to be done is to modify the available {@link StrategySettingsDefinition}
 * in {@link JavaCardDLStrategy.Factory#getSettingsDefinition()}.
 * </p>
 * <p>
 * As future work this class should not show a fixed content defined
 * by {@link #DEFINITION}. Instead it should update the UI controls based
 * on the currently active proof and its {@link Profile} since different
 * {@link Profile}s support different {@link Strategy}s with different
 * {@link StrategyProperties}. For more information have a look at:
 * {@code http://i12www.ira.uka.de/~klebanov/mantis/view.php?id=1359}
 * </p>
 * @author Martin Hentschel
 */
public final class StrategySelectionView extends JPanel {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = -267867794853527874L;

   /**
    * The always used {@link StrategyFactory}.
    */
   private static final StrategyFactory FACTORY = JavaProfile.DEFAULT;

   /**
    * The {@link StrategySettingsDefinition} of {@link #FACTORY} which defines the UI controls to show.
    */
   private static final StrategySettingsDefinition DEFINITION = FACTORY.getSettingsDefinition();

   /**
    * The name of {@link #FACTORY}.
    */
   private static final String JAVACARDDL_STRATEGY_NAME = FACTORY.name().toString();

   /**
    * Observe changes on {@link #mediator}.
    */
   private final KeYSelectionListener mediatorListener = new KeYSelectionListener() {
      public void selectedNodeChanged(KeYSelectionEvent e) {
      }

      public void selectedProofChanged(KeYSelectionEvent e) {
         refresh(e.getSource().getSelectedProof());
      }
   };

   /**
    * The {@link MainWindow} in which this {@link StrategySelectionView} is shown.
    */
   private final MainWindow mainWindow;

   /**
    * The {@link KeYMediator} which provides the active proof.
    */
   private KeYMediator mediator;

   /**
    * Allows access to shown UI controls generated according to {@link #DEFINITION}.
    */
   private StrategySelectionComponents components;

   public StrategySelectionView(MainWindow mainWindow) {
      this.mainWindow = mainWindow;
      layoutPane();
      refresh(mediator == null ? null : mediator.getSelectedProof());
      setVisible(true);
      addComponentListener(new java.awt.event.ComponentAdapter() {
         public void componentShown(java.awt.event.ComponentEvent e) {
            components.getMaxRuleAppSlider().refresh();
         }
      });
   }

   /** Build everything */
   private void layoutPane() {
      assert components == null : "Content can not be created a second time!";
      components = new StrategySelectionComponents();

      JPanel javaDLOptionsPanel = new JPanel();

      JScrollPane javaDLOptionsScrollPane = new JScrollPane(javaDLOptionsPanel,
                                                            ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
                                                            ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER);

      javaDLOptionsPanel.setEnabled(true);

      this.setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));

      GridBagConstraints gbcpanel5 = new GridBagConstraints();
      final GridBagLayout javaDLOptionsLayout = new GridBagLayout();
      javaDLOptionsPanel.setLayout(javaDLOptionsLayout);

      javaDLOptionsScrollPane.getVerticalScrollBar().setUnitIncrement(10);

      // //////////////////////////////////////////////////////////////////////

      JButton go = new JButton(mainWindow.getAutoModeAction());

      JPanel timeout = createDefaultPanel(components);

      JPanel goPanel = new JPanel();
      GridBagLayout goLayout = new GridBagLayout();
      goPanel.setLayout(goLayout);
      goPanel.setAlignmentX(Component.LEFT_ALIGNMENT);

      gbcpanel5.gridx = 1;
      gbcpanel5.gridy = 0;
      gbcpanel5.gridwidth = 1;
      gbcpanel5.gridheight = 1;
      gbcpanel5.fill = GridBagConstraints.NONE;
      gbcpanel5.weightx = 1;
      gbcpanel5.weighty = 0;
      gbcpanel5.anchor = GridBagConstraints.WEST;
      gbcpanel5.insets = new Insets(4, 4, 4, 4);
      goLayout.setConstraints(go, gbcpanel5);
      goPanel.add(go);

      gbcpanel5.gridx = 2;
      gbcpanel5.gridy = 0;
      gbcpanel5.gridwidth = 1;
      gbcpanel5.gridheight = 1;
      gbcpanel5.fill = GridBagConstraints.NONE;
      gbcpanel5.weightx = 1;
      gbcpanel5.weighty = 0;
      gbcpanel5.anchor = GridBagConstraints.WEST;
      gbcpanel5.insets = new Insets(0, 0, 0, 0);

      gbcpanel5.gridx = 3;
      gbcpanel5.gridy = 0;
      gbcpanel5.gridwidth = 1;
      gbcpanel5.gridheight = 1;
      gbcpanel5.fill = GridBagConstraints.NONE;
      gbcpanel5.weightx = 0;
      gbcpanel5.weighty = 0;
      gbcpanel5.anchor = GridBagConstraints.CENTER;
      gbcpanel5.insets = new Insets(0, 0, 0, 0);
      goLayout.setConstraints(timeout, gbcpanel5);
      goPanel.add(timeout);

      fixVerticalSpace(goPanel);

      Box box = Box.createVerticalBox();
      box.add(Box.createVerticalStrut(4));
      box.add(goPanel);
      box.add(Box.createVerticalStrut(8));

      if (DEFINITION.isShowMaxRuleApplications()) {
         MaxRuleAppSlider maxSlider = new MaxRuleAppSlider(mediator, DEFINITION.getMaxRuleApplicationsLabel());
         components.setMaxRuleAppSlider(maxSlider);
         maxSlider.addChangeListener(new ChangeListener() {
            public void stateChanged(ChangeEvent e) {
               refreshDefaultButton();
            }
         });
         maxSlider.setAlignmentX(Component.LEFT_ALIGNMENT);
         box.add(maxSlider);
         box.add(Box.createVerticalStrut(8));
      }

      javaDLOptionsScrollPane.setAlignmentX(Component.LEFT_ALIGNMENT);
      box.add(javaDLOptionsScrollPane);

      // //////////////////////////////////////////////////////////////////////

      if (!DEFINITION.getProperties().isEmpty()) {
         javaDLOptionsScrollPane.setBorder(BorderFactory.createTitledBorder(DEFINITION.getPropertiesTitle()));
         javaDLOptionsPanel.setLayout(javaDLOptionsLayout);

         javaDLOptionsScrollPane.getVerticalScrollBar().setUnitIncrement(10);
         javaDLOptionsScrollPane.setAlignmentX(Component.LEFT_ALIGNMENT);
         box.add(javaDLOptionsScrollPane);

         int yCoord = 0;
         for (AbstractStrategyPropertyDefinition definition : DEFINITION.getProperties()) {
            yCoord = createStrategyProperty(components, 
                                            FACTORY, 
                                            javaDLOptionsPanel, 
                                            javaDLOptionsLayout, 
                                            yCoord, 
                                            true, 
                                            definition);
         }

         fixVerticalSpace(javaDLOptionsScrollPane);
      }

      // //////////////////////////////////////////////////////////////////////

      this.add(box);
   }

   protected int createStrategyProperty(StrategySelectionComponents data,
                                        StrategyFactory factory, 
                                        JPanel javaDLOptionsPanel, 
                                        GridBagLayout javaDLOptionsLayout, 
                                        int yCoord, 
                                        boolean topLevel, 
                                        AbstractStrategyPropertyDefinition definition) {

      // Individual options
      if (definition instanceof OneOfStrategyPropertyDefinition) {
         OneOfStrategyPropertyDefinition oneOfDefinition = (OneOfStrategyPropertyDefinition) definition;
         ButtonGroup buttonGroup = new ButtonGroup();
         if (!oneOfDefinition.getValues().isEmpty()) {
            data.addPropertyGroup(oneOfDefinition.getApiKey(), buttonGroup);
         }
         ++yCoord;

         JLabel label = new JLabel(oneOfDefinition.getName());
         label.setToolTipText(oneOfDefinition.getTooltip());
         if (topLevel) {
            addJavaDLOption(javaDLOptionsPanel, label, javaDLOptionsLayout, 1, yCoord, 7);

            ++yCoord;

            int gridx = 0;
            int column = 0;
            for (StrategyPropertyValueDefinition valueDefinition : oneOfDefinition.getValues()) {
               gridx += 2;
               JRadioButton radioButton = newButton(valueDefinition.getValue(), oneOfDefinition.getApiKey(), valueDefinition.getApiValue(), true, false, factory);
               data.addPropertyButton(radioButton, oneOfDefinition.getApiKey());
               radioButton.setToolTipText(valueDefinition.getTooltip());
               buttonGroup.add(radioButton);
               addJavaDLOption(javaDLOptionsPanel, 
                               radioButton, 
                               javaDLOptionsLayout,
                               valueDefinition.getSwingGridx() >= 0 ? valueDefinition.getSwingGridx() : gridx,
                               yCoord,
                               valueDefinition.getSwingWidth() >= 0 ? valueDefinition.getSwingWidth() : 2);
               column++;
               if (oneOfDefinition.getColumnsPerRow() >= 0 && column % oneOfDefinition.getColumnsPerRow() == 0) {
                  gridx = 0;
                  ++yCoord;
               }
            }
         }
         else {
            if (oneOfDefinition.getValues().get(0).getSwingGridx() >= 0) {
               addJavaDLOption(javaDLOptionsPanel, label, javaDLOptionsLayout, 2, yCoord, 1);

               int gridx = 0;
               int column = 0;
               for (StrategyPropertyValueDefinition valueDefinition : oneOfDefinition.getValues()) {
                  gridx += 2;
                  JRadioButton radioButton = newButton(valueDefinition.getValue(),
                                                       oneOfDefinition.getApiKey(),
                                                       valueDefinition.getApiValue(), 
                                                       true, 
                                                       false, 
                                                       factory);
                  data.addPropertyButton(radioButton, oneOfDefinition.getApiKey());
                  radioButton.setToolTipText(valueDefinition.getTooltip());
                  buttonGroup.add(radioButton);
                  addJavaDLOption(javaDLOptionsPanel,
                                  radioButton,
                                  javaDLOptionsLayout,
                                  valueDefinition.getSwingGridx() >= 0 ? valueDefinition.getSwingGridx() : gridx,
                                  yCoord,
                                  valueDefinition.getSwingWidth() >= 0 ? valueDefinition.getSwingWidth() : 2);
                  column++;
                  if (oneOfDefinition.getColumnsPerRow() >= 0 && column % oneOfDefinition.getColumnsPerRow() == 0) {
                     gridx = 0;
                     ++yCoord;
                  }
               }
            }
            else {
               JPanel queryAxiomPanel = new JPanel();
               queryAxiomPanel.add(label);
               for (StrategyPropertyValueDefinition valueDefinition : oneOfDefinition.getValues()) {
                  JRadioButton radioButton = newButton(valueDefinition.getValue(),
                                                       oneOfDefinition.getApiKey(),
                                                       valueDefinition.getApiValue(), 
                                                       true, 
                                                       false, 
                                                       factory);
                  data.addPropertyButton(radioButton, oneOfDefinition.getApiKey());
                  radioButton.setToolTipText(valueDefinition.getTooltip());
                  buttonGroup.add(radioButton);
                  queryAxiomPanel.add(radioButton);
               }

               addJavaDLOption(javaDLOptionsPanel, queryAxiomPanel, javaDLOptionsLayout, 2, yCoord, 7);
            }
         }

         ++yCoord;

         addJavaDLOptionSpace(javaDLOptionsPanel, javaDLOptionsLayout, yCoord);
      }
      else {
         throw new RuntimeException("Unsupported property definition \"" + definition + "\".");
      }
      // Create sub properties
      for (AbstractStrategyPropertyDefinition subProperty : definition.getSubProperties()) {
         yCoord = createStrategyProperty(data, 
                                         factory, 
                                         javaDLOptionsPanel, 
                                         javaDLOptionsLayout, 
                                         yCoord, 
                                         false, 
                                         subProperty);
      }
      return yCoord;
   }

   private JRadioButton newButton(String text, 
                                  final String key, 
                                  final String command, 
                                  boolean selected, 
                                  boolean enabled, 
                                  final StrategyFactory factory) {
      JRadioButton result = new JRadioButton(text);
      result.addActionListener(new ActionListener() {
         @Override
         public void actionPerformed(ActionEvent e) {
            StrategyProperties props = getProperties();
            updateStrategySettings(mediator.getSelectedProof().getActiveStrategy().name().toString(), props);
         }
      });
      result.setEnabled(enabled);
      result.setActionCommand(command);
      return result;
   }

   private void addJavaDLOptionSpace(JPanel javaDLOptionsPanel, GridBagLayout javaDLOptionsLayout, int yCoord) {
      final GridBagConstraints con = new GridBagConstraints();
      con.gridx = 0;
      con.gridy = yCoord;
      con.gridwidth = 9;
      con.gridheight = 1;
      con.fill = GridBagConstraints.HORIZONTAL;
      con.weightx = 1;
      con.weighty = 0;
      con.anchor = GridBagConstraints.CENTER;
      final Component sep = new JLabel();
      javaDLOptionsLayout.setConstraints(sep, con);
      javaDLOptionsPanel.add(sep);
      addJavaDLOption(javaDLOptionsPanel, Box.createRigidArea(new Dimension(4, 4)), javaDLOptionsLayout, 0, yCoord, 1);
      addJavaDLOption(javaDLOptionsPanel, Box.createRigidArea(new Dimension(4, 4)), javaDLOptionsLayout, 1, yCoord, 1);
   }

   private void addJavaDLOption(JPanel javaDLOptionsPanel, Component widget, GridBagLayout javaDLOptionsLayout, int gridx, int gridy, int width) {
      final GridBagConstraints con = new GridBagConstraints();
      con.gridx = gridx;
      con.gridy = gridy;
      con.gridwidth = width;
      con.gridheight = 1;
      con.fill = GridBagConstraints.NONE;
      con.weightx = 0;
      con.weighty = 0;
      con.anchor = GridBagConstraints.WEST;
      javaDLOptionsLayout.setConstraints(widget, con);
      javaDLOptionsPanel.add(widget);
   }

   private void fixVerticalSpace(JComponent comp) {
      comp.setMaximumSize(new Dimension(Integer.MAX_VALUE, comp.getPreferredSize().height));
   }

   private JPanel createDefaultPanel(StrategySelectionComponents components) {
      final JPanel panel = new JPanel();
      JButton defaultButton = new JButton("Defaults");
      components.setDefaultButton(defaultButton);
      defaultButton.addActionListener(new ActionListener() {
         public void actionPerformed(ActionEvent e) {
            mediator.getSelectedProof().getSettings().getStrategySettings().setMaxSteps(DEFINITION.getDefaultMaxRuleApplications());
            updateStrategySettings(JAVACARDDL_STRATEGY_NAME, DEFINITION.getDefaultPropertiesFactory().createDefaultStrategyProperties());
            refresh(mediator.getSelectedProof());
         }
      });
      panel.add(defaultButton);
      return panel;
   }

   public void setMediator(KeYMediator mediator) {
      if (this.mediator != null) {
         this.mediator.removeKeYSelectionListener(mediatorListener);
      }
      this.mediator = mediator;
      if (components.getMaxRuleAppSlider() != null) {
         components.getMaxRuleAppSlider().setMediator(this.mediator);
      }
      if (this.mediator != null) {
         this.mediator.addKeYSelectionListener(mediatorListener);
      }
   }

   /** performs a refresh of all elements in this tab */
   public void refresh(Proof proof) {
      if (proof == null) {
         enableAll(false);
      }
      else {
         if (components.getMaxRuleAppSlider() != null) {
            components.getMaxRuleAppSlider().refresh();
         }
         StrategyProperties sp = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
         for (Entry<String, List<JRadioButton>> entry : components.getPropertyButtons().entrySet()) {
            String value = sp.getProperty(entry.getKey());
            for (JRadioButton button : entry.getValue()) {
               button.setSelected(JavaUtil.equals(button.getActionCommand(), value));
            }
         }
         enableAll(true);

         refreshDefaultButton();
      }
   }

   private void refreshDefaultButton() {
      if (mediator.getSelectedProof() != null) {
         boolean defaultMaxRules = components.getMaxRuleAppSlider() == null ||
                                   components.getMaxRuleAppSlider().getPos() == DEFINITION.getDefaultMaxRuleApplications();
         boolean defaultProperties = getProperties().equals(DEFINITION.getDefaultPropertiesFactory().createDefaultStrategyProperties());
         components.getDefaultButton().setEnabled(!defaultMaxRules || !defaultProperties);
      }
      else {
         components.getDefaultButton().setEnabled(false);
      }
   }

   /**
    * enables or disables all components
    * 
    * @param enable
    *           boolean saying whether to activate or deactivate the components
    */
   private void enableAll(boolean enable) {
      if (components.getMaxRuleAppSlider() != null) {
         components.getMaxRuleAppSlider().setEnabled(enable);
      }
      components.getDefaultButton().setEnabled(enable);
      for (Entry<String, List<JRadioButton>> entry : components.getPropertyButtons().entrySet()) {
         for (JRadioButton button : entry.getValue()) {
            button.setEnabled(enable);
         }
      }
   }

   public Strategy getStrategy(String strategyName, Proof proof, StrategyProperties properties) {
      if (mediator != null) {
         Iterator<StrategyFactory> supportedStrategies = mediator.getProfile().supportedStrategies().iterator();
         while (supportedStrategies.hasNext()) {
            final StrategyFactory s = supportedStrategies.next();
            if (strategyName.equals(s.name().toString())) {
               return s.create(proof, properties);
            }
         }
         System.err.println("Selected Strategy '" + strategyName + "' not found falling back to " + mediator.getProfile().getDefaultStrategyFactory().name());
      }
      return mediator != null ? 
             mediator.getProfile().getDefaultStrategyFactory().create(proof, properties) : 
             proof.getServices().getProfile().getDefaultStrategyFactory().create(proof, properties);
   }

   /**
    * @return the StrategyProperties
    */
   private StrategyProperties getProperties() {
      StrategyProperties p = new StrategyProperties();

      for (Entry<String, ButtonGroup> entry : components.getPropertyGroups().entrySet()) {
         ButtonModel selected = entry.getValue().getSelection();
         if (selected != null) {
            p.setProperty(entry.getKey(), selected.getActionCommand());
         }
         else {
            p.setProperty(entry.getKey(), DEFINITION.getDefaultPropertiesFactory().createDefaultStrategyProperties().getProperty(entry.getKey()));
         }
      }

      return p;
   }

   private void updateStrategySettings(String strategyName, StrategyProperties p) {
      final Proof proof = mediator.getSelectedProof();
      final Strategy strategy = getStrategy(strategyName, proof, p);

      ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setStrategy(strategy.name());
      ProofSettings.DEFAULT_SETTINGS.getStrategySettings().setActiveStrategyProperties(p);

      proof.getSettings().getStrategySettings().setStrategy(strategy.name());
      proof.getSettings().getStrategySettings().setActiveStrategyProperties(p);

      proof.setActiveStrategy(strategy);

      refresh(proof);
   }

   /**
    * Provided via
    * {@link StrategySelectionView#getStrategySelectionComponents()} for direct
    * access to created user interface components.
    * 
    * @author Martin Hentschel
    */
   private static class StrategySelectionComponents {
      /**
       * The {@link MaxRuleAppSlider} in which the maximal number of steps is
       * edited.
       */
      private MaxRuleAppSlider maxRuleAppSlider;

      /**
       * Maps a property key to the {@link JRadioButton}s which defines the
       * values.
       */
      private Map<String, List<JRadioButton>> propertyButtons = new HashMap<String, List<JRadioButton>>();

      /**
       * Maps a property to the used {@link ButtonGroup}.
       */
      private Map<String, ButtonGroup> propertyGroups = new HashMap<String, ButtonGroup>();

      /**
       * The {@link JButton} which restores default values.
       */
      private JButton defaultButton;

      /**
       * Returns the {@link MaxRuleAppSlider} in which the maximal number of
       * steps is edited.
       * 
       * @return The {@link MaxRuleAppSlider} in which the maximal number of
       *         steps is edited.
       */
      public MaxRuleAppSlider getMaxRuleAppSlider() {
         return maxRuleAppSlider;
      }

      /**
       * Sets the {@link MaxRuleAppSlider} in which the maximal number of steps
       * is edited.
       * 
       * @param maxRuleAppSlider
       *           The {@link MaxRuleAppSlider} in which the maximal number of
       *           steps is edited.
       */
      public void setMaxRuleAppSlider(MaxRuleAppSlider maxRuleAppSlider) {
         this.maxRuleAppSlider = maxRuleAppSlider;
      }

      /**
       * Registers the given {@link JRadioButton} for the given key.
       * 
       * @param button
       *           The {@link JRadioButton}.
       * @param key
       *           The key.
       */
      public void addPropertyButton(JRadioButton button, String key) {
         List<JRadioButton> buttons = propertyButtons.get(key);
         if (buttons == null) {
            buttons = new LinkedList<JRadioButton>();
            propertyButtons.put(key, buttons);
         }
         buttons.add(button);
      }

      /**
       * Returns the mapping of property keys to the {@link JRadioButton}s which
       * defines the values.
       * 
       * @return The mapping of property keys to the {@link JRadioButton}s which
       *         defines the values.
       */
      public Map<String, List<JRadioButton>> getPropertyButtons() {
         return propertyButtons;
      }

      /**
       * Returns the {@link JButton} which restores default values.
       * 
       * @return The {@link JButton} which restores default values.
       */
      public JButton getDefaultButton() {
         return defaultButton;
      }

      /**
       * Sets the {@link JButton} which restores default values.
       * 
       * @param defaultButton
       *           The {@link JButton} which restores default values.
       */
      public void setDefaultButton(JButton defaultButton) {
         this.defaultButton = defaultButton;
      }

      /**
       * Returns the {@link Map} of properties to {@link ButtonGroup}s.
       * 
       * @return The {@link Map} of properties to {@link ButtonGroup}s.
       */
      public Map<String, ButtonGroup> getPropertyGroups() {
         return propertyGroups;
      }

      /**
       * Adds the property group.
       * 
       * @param property
       *           The property.
       * @param group
       *           The {@link ButtonGroup}.
       */
      public void addPropertyGroup(String property, ButtonGroup group) {
         propertyGroups.put(property, group);
      }
   }
}
