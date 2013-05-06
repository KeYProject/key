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

package org.key_project.keyide.ui.composite;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ScrolledForm;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.StrategyProperties;

public class StrategyPropertiesScrolledForm extends ScrolledForm {
   
   private Proof proof;
   
   private StrategyProperties props = new StrategyProperties();

   private Text maxStepText;
   private Button stopAtDefault;
   private Button stopAtUnclosable;
   private Button treatmentOfNewUnclosableGoalsNone;
   private Button treatmentOfNewUnclosableGoalsAutoPrune;
   private Button logicalSplittingDelayed;
   private Button logicalSplittingFree;
   private Button logicalSplittingOff;
   private Button loopTreatmentInvariant;
   private Button loopTreatmentExpand;
   private Button loopTreatmentNone;
   private Button blockTreatmentContract;
   private Button blockTreatmentExpand;
   private Button methodTreatmentContract;
   private Button methodTreatmentExpand;
   private Button methodTreatmentNone;
   private Button dependencyContratcsOn;
   private Button dependencyContratcsOff;
   private Button queryTreatmentOn;
   private Button queryTreatmentRestricted;
   private Button queryTreatmentOff;
   private Button expandLocalQueriesOn;
   private Button expandLocalQueriesOff;
   private Button arithmeticTreatmentBasic;
   private Button arithmeticTreatmentDefOps;
   private Button arithmeticTreatmentModelSearch;
   private Button quantifierTreatmentNone;
   private Button quantifierTreatmentNoSplits;
   private Button quantifierTreatmentNoSplitsWithProgs;
   private Button quantifierTreatmentFree;
   private Button autoInductionOn;
   private Button autoInductionRestricted;
   private Button autoInductionOff;
   private Button userSpecificTacletsOneOff;
   private Button userSpecificTacletsOneLowPrior;
   private Button userSpecificTacletsOneHighPrior;
   private Button userSpecificTacletsTwoOff;
   private Button userSpecificTacletsTwoLowPrior;
   private Button userSpecificTacletsTwoHighPrior;
   private Button userSpecificTacletsThreeOff;
   private Button userSpecificTacletsThreeLowPrior;
   private Button userSpecificTacletsThreeHighPrior;

   public StrategyPropertiesScrolledForm(Composite parent) {
      super(parent, SWT.V_SCROLL);
      initializeContent(parent);
   }
   
   private void initializeContent(Composite parent) {
      FormToolkit toolkit = new FormToolkit(parent.getDisplay());
      getBody().setLayout(new GridLayout(1, false));
      getBody().setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      
      Label maxStepLabel = new Label(getBody(), SWT.NONE);
      maxStepLabel.setText("&Maximum number of steps:");
      maxStepText = new Text(getBody(), SWT.BORDER);
      maxStepText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      maxStepText.addModifyListener(maxStepListener);
      maxStepText.setTextLimit(7);
      
      Group javaDLOptionsGroup = new Group(getBody(), SWT.SHADOW_IN);
      javaDLOptionsGroup.setLayout(new GridLayout());
      javaDLOptionsGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      javaDLOptionsGroup.setText("Java DL Options");
      
      Group stopAtGroup = new Group(javaDLOptionsGroup, SWT.SHADOW_IN);
      stopAtGroup.setText("Stop at");
      stopAtGroup.setLayout(new GridLayout());
      stopAtGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      stopAtDefault = toolkit.createButton(stopAtGroup, "Default", SWT.RADIO);
      stopAtUnclosable = toolkit.createButton(stopAtGroup, "Unclosable", SWT.RADIO);
      stopAtDefault.addSelectionListener(listener);
      stopAtUnclosable.addSelectionListener(listener);

      
      Group treatmentOfNewUnclosableGoalsGroup = new Group(javaDLOptionsGroup, SWT.SHADOW_IN);
      treatmentOfNewUnclosableGoalsGroup.setText("Treatment of new unclosable goals");
      treatmentOfNewUnclosableGoalsGroup.setLayout(new GridLayout());
      treatmentOfNewUnclosableGoalsGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      treatmentOfNewUnclosableGoalsNone = toolkit.createButton(treatmentOfNewUnclosableGoalsGroup, "None", SWT.RADIO);
      treatmentOfNewUnclosableGoalsAutoPrune = toolkit.createButton(treatmentOfNewUnclosableGoalsGroup, "AutoPrune", SWT.RADIO);
      treatmentOfNewUnclosableGoalsNone.addSelectionListener(listener);
      treatmentOfNewUnclosableGoalsAutoPrune.addSelectionListener(listener);
      
      Group logicalSplittingGroup = new Group(javaDLOptionsGroup, SWT.SHADOW_IN);
      logicalSplittingGroup.setText("Logical splitting");
      logicalSplittingGroup.setLayout(new GridLayout());
      logicalSplittingGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      logicalSplittingDelayed = toolkit.createButton(logicalSplittingGroup, "Delayed", SWT.RADIO);
      logicalSplittingFree = toolkit.createButton(logicalSplittingGroup, "Free", SWT.RADIO);
      logicalSplittingOff = toolkit.createButton(logicalSplittingGroup, "Off", SWT.RADIO);
      logicalSplittingDelayed.addSelectionListener(listener);
      logicalSplittingFree.addSelectionListener(listener);
      logicalSplittingOff.addSelectionListener(listener);
      
      Group loopTreatmentGroup = new Group(javaDLOptionsGroup, SWT.SHADOW_IN);
      loopTreatmentGroup.setText("Loop treatment");
      loopTreatmentGroup.setLayout(new GridLayout());
      loopTreatmentGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      loopTreatmentInvariant = toolkit.createButton(loopTreatmentGroup, "Invariant", SWT.RADIO);
      loopTreatmentExpand = toolkit.createButton(loopTreatmentGroup, "Expand", SWT.RADIO);
      loopTreatmentNone = toolkit.createButton(loopTreatmentGroup, "None", SWT.RADIO);
      loopTreatmentInvariant.addSelectionListener(listener);
      loopTreatmentExpand.addSelectionListener(listener);
      loopTreatmentNone.addSelectionListener(listener);
      
      Group blockTreatmentGroup = new Group(javaDLOptionsGroup, SWT.SHADOW_IN);
      blockTreatmentGroup.setText("Block treatment");
      blockTreatmentGroup.setLayout(new GridLayout());
      blockTreatmentGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      blockTreatmentContract = toolkit.createButton(blockTreatmentGroup, "Contract", SWT.RADIO);
      blockTreatmentExpand = toolkit.createButton(blockTreatmentGroup, "Expand", SWT.RADIO);
      blockTreatmentContract.addSelectionListener(listener);
      blockTreatmentExpand.addSelectionListener(listener);
      
      Group methodTreatmentGroup = new Group(javaDLOptionsGroup, SWT.SHADOW_IN);
      methodTreatmentGroup.setText("Method treatment");
      methodTreatmentGroup.setLayout(new GridLayout());
      methodTreatmentGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      methodTreatmentContract = toolkit.createButton(methodTreatmentGroup, "Contract", SWT.RADIO);
      methodTreatmentExpand = toolkit.createButton(methodTreatmentGroup, "Expand", SWT.RADIO);
      methodTreatmentNone = toolkit.createButton(methodTreatmentGroup, "None", SWT.RADIO);
      methodTreatmentContract.addSelectionListener(listener);
      methodTreatmentExpand.addSelectionListener(listener);
      methodTreatmentNone.addSelectionListener(listener);
      
      Group dependencyContratcsGroup = new Group(javaDLOptionsGroup, SWT.SHADOW_IN);
      dependencyContratcsGroup.setText("Dependency contracts");
      dependencyContratcsGroup.setLayout(new GridLayout());
      dependencyContratcsGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      dependencyContratcsOn = toolkit.createButton(dependencyContratcsGroup, "On", SWT.RADIO);
      dependencyContratcsOff = toolkit.createButton(dependencyContratcsGroup, "Off", SWT.RADIO);
      dependencyContratcsOn.addSelectionListener(listener);
      dependencyContratcsOff.addSelectionListener(listener);
      
      Group queryTreatmentGroup = new Group(javaDLOptionsGroup, SWT.SHADOW_IN);
      queryTreatmentGroup.setText("Query treatment");
      GridLayout queryLayout = new GridLayout();
      queryLayout.numColumns=3;
      queryTreatmentGroup.setLayout(queryLayout);
      queryTreatmentGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      queryTreatmentOn = toolkit.createButton(queryTreatmentGroup, "On", SWT.RADIO);
      queryTreatmentRestricted = toolkit.createButton(queryTreatmentGroup, "Restricted", SWT.RADIO);
      queryTreatmentOff = toolkit.createButton(queryTreatmentGroup, "Off", SWT.RADIO);
      queryTreatmentOn.addSelectionListener(listener);
      queryTreatmentRestricted.addSelectionListener(listener);
      queryTreatmentOff.addSelectionListener(listener);
      
      Group expandLocalQueriesGroup = new Group(queryTreatmentGroup, SWT.SHADOW_IN);
      expandLocalQueriesGroup.setText("Expand local queries");
      expandLocalQueriesGroup.setLayout(new GridLayout());
      expandLocalQueriesGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      expandLocalQueriesOn = toolkit.createButton(expandLocalQueriesGroup, "On", SWT.RADIO);
      expandLocalQueriesOff = toolkit.createButton(expandLocalQueriesGroup, "Off", SWT.RADIO);
      expandLocalQueriesOn.addSelectionListener(listener);
      expandLocalQueriesOff.addSelectionListener(listener);
      
      Group arithmeticTreatmentGroup = new Group(javaDLOptionsGroup, SWT.SHADOW_IN);
      arithmeticTreatmentGroup.setText("Arithmetic treatment");
      arithmeticTreatmentGroup.setLayout(new GridLayout());
      arithmeticTreatmentGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      arithmeticTreatmentBasic = toolkit.createButton(arithmeticTreatmentGroup, "Basic", SWT.RADIO);
      arithmeticTreatmentDefOps = toolkit.createButton(arithmeticTreatmentGroup, "DefOps", SWT.RADIO);
      arithmeticTreatmentModelSearch = toolkit.createButton(arithmeticTreatmentGroup, "Model Search", SWT.RADIO);
      arithmeticTreatmentBasic.addSelectionListener(listener);
      arithmeticTreatmentDefOps.addSelectionListener(listener);
      arithmeticTreatmentModelSearch.addSelectionListener(listener);
      
      Group quantifierTreatmentGroup = new Group(javaDLOptionsGroup, SWT.SHADOW_IN);
      quantifierTreatmentGroup.setText("Quantifier treatment");
      GridLayout quantifierLayout = new GridLayout();
      quantifierLayout.numColumns=2;
      quantifierTreatmentGroup.setLayout(quantifierLayout);
      quantifierTreatmentGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      quantifierTreatmentNone = toolkit.createButton(quantifierTreatmentGroup, "None", SWT.RADIO);
      quantifierTreatmentNoSplits = toolkit.createButton(quantifierTreatmentGroup, "No Splits", SWT.RADIO);
      quantifierTreatmentNoSplitsWithProgs = toolkit.createButton(quantifierTreatmentGroup, "No Splits with Progs", SWT.RADIO);
      quantifierTreatmentFree = toolkit.createButton(quantifierTreatmentGroup, "Free", SWT.RADIO);
      quantifierTreatmentNone.addSelectionListener(listener);
      quantifierTreatmentNoSplits.addSelectionListener(listener);
      quantifierTreatmentNoSplitsWithProgs.addSelectionListener(listener);
      quantifierTreatmentFree.addSelectionListener(listener);
      
      Group autoInductionGroup = new Group(javaDLOptionsGroup, SWT.SHADOW_IN);
      autoInductionGroup.setText("Auto Induction");
      autoInductionGroup.setLayout(new GridLayout());
      autoInductionGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      autoInductionOn = toolkit.createButton(autoInductionGroup, "On", SWT.RADIO);
      autoInductionRestricted = toolkit.createButton(autoInductionGroup, "Restricted", SWT.RADIO);
      autoInductionOff = toolkit.createButton(autoInductionGroup, "Off", SWT.RADIO);
      autoInductionOn.addSelectionListener(listener);
      autoInductionRestricted.addSelectionListener(listener);
      autoInductionOff.addSelectionListener(listener);
      
      Group userSpecificTacletsGroup = new Group(javaDLOptionsGroup, SWT.SHADOW_IN);
      userSpecificTacletsGroup.setText("User-specific taclets");
      GridLayout tacletLayout = new GridLayout();
      tacletLayout.numColumns=1;
      userSpecificTacletsGroup.setLayout(tacletLayout);
      userSpecificTacletsGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));      
      
      Group firstUserSpecificTacletsGroup = new Group(userSpecificTacletsGroup, SWT.SHADOW_IN);
      firstUserSpecificTacletsGroup.setText("1:");
      firstUserSpecificTacletsGroup.setLayout(new GridLayout());
      firstUserSpecificTacletsGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      userSpecificTacletsOneOff = toolkit.createButton(firstUserSpecificTacletsGroup, "Off", SWT.RADIO);
      userSpecificTacletsOneLowPrior = toolkit.createButton(firstUserSpecificTacletsGroup, "Low prior.", SWT.RADIO);
      userSpecificTacletsOneHighPrior = toolkit.createButton(firstUserSpecificTacletsGroup, "High prior.", SWT.RADIO);
      userSpecificTacletsOneOff.addSelectionListener(listener);
      userSpecificTacletsOneLowPrior.addSelectionListener(listener);
      userSpecificTacletsOneHighPrior.addSelectionListener(listener);
      
      Group secondUserSpecificTacletsGroup = new Group(userSpecificTacletsGroup, SWT.SHADOW_IN);
      secondUserSpecificTacletsGroup.setText("2:");
      secondUserSpecificTacletsGroup.setLayout(new GridLayout());
      secondUserSpecificTacletsGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      userSpecificTacletsTwoOff = toolkit.createButton(secondUserSpecificTacletsGroup, "Off", SWT.RADIO);
      userSpecificTacletsTwoLowPrior = toolkit.createButton(secondUserSpecificTacletsGroup, "Low prior.", SWT.RADIO);
      userSpecificTacletsTwoHighPrior = toolkit.createButton(secondUserSpecificTacletsGroup, "High prior.", SWT.RADIO);
      userSpecificTacletsTwoOff.addSelectionListener(listener);
      userSpecificTacletsTwoLowPrior.addSelectionListener(listener);
      userSpecificTacletsTwoHighPrior.addSelectionListener(listener);
      
      Group thirdUserSpecificTacletsGroup = new Group(userSpecificTacletsGroup, SWT.SHADOW_IN);
      thirdUserSpecificTacletsGroup.setText("3:");
      thirdUserSpecificTacletsGroup.setLayout(new GridLayout());
      thirdUserSpecificTacletsGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      userSpecificTacletsThreeOff = toolkit.createButton(thirdUserSpecificTacletsGroup, "Off", SWT.RADIO);
      userSpecificTacletsThreeLowPrior = toolkit.createButton(thirdUserSpecificTacletsGroup, "Low prior.", SWT.RADIO);
      userSpecificTacletsThreeHighPrior = toolkit.createButton(thirdUserSpecificTacletsGroup, "High prior.", SWT.RADIO);
      userSpecificTacletsThreeOff.addSelectionListener(listener);
      userSpecificTacletsThreeLowPrior.addSelectionListener(listener);
      userSpecificTacletsThreeHighPrior.addSelectionListener(listener);
  }

   public void setProof(Proof proof){
      this.proof = proof;
   }


   public void setContent(){
      props = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
      
      maxStepText.setText(String.valueOf(proof.getSettings().getStrategySettings().getMaxSteps()));
      
      stopAtDefault.setSelection(props.getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY).equals(StrategyProperties.STOPMODE_DEFAULT));
      stopAtUnclosable.setSelection(props.getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY).equals(StrategyProperties.STOPMODE_NONCLOSE));
      treatmentOfNewUnclosableGoalsNone.setSelection(props.getProperty(StrategyProperties.RETREAT_MODE_OPTIONS_KEY).equals(StrategyProperties.RETREAT_MODE_NONE));
      treatmentOfNewUnclosableGoalsAutoPrune.setSelection(props.getProperty(StrategyProperties.RETREAT_MODE_OPTIONS_KEY).equals(StrategyProperties.RETREAT_MODE_RETREAT));
      logicalSplittingDelayed.setSelection(props.getProperty(StrategyProperties.SPLITTING_OPTIONS_KEY).equals(StrategyProperties.SPLITTING_DELAYED));
      logicalSplittingFree.setSelection(props.getProperty(StrategyProperties.SPLITTING_OPTIONS_KEY).equals(StrategyProperties.SPLITTING_NORMAL));
      logicalSplittingOff.setSelection(props.getProperty(StrategyProperties.SPLITTING_OPTIONS_KEY).equals(StrategyProperties.SPLITTING_OFF));
      loopTreatmentInvariant.setSelection(props.getProperty(StrategyProperties.LOOP_OPTIONS_KEY).equals(StrategyProperties.LOOP_INVARIANT));
      loopTreatmentExpand.setSelection(props.getProperty(StrategyProperties.LOOP_OPTIONS_KEY).equals(StrategyProperties.LOOP_EXPAND));
      loopTreatmentNone.setSelection(props.getProperty(StrategyProperties.LOOP_OPTIONS_KEY).equals(StrategyProperties.LOOP_NONE));
      //LOOP_BOUNDED?
      blockTreatmentContract.setSelection(props.getProperty(StrategyProperties.BLOCK_OPTIONS_KEY).equals(StrategyProperties.BLOCK_CONTRACT));
      blockTreatmentExpand.setSelection(props.getProperty(StrategyProperties.BLOCK_OPTIONS_KEY).equals(StrategyProperties.BLOCK_EXPAND));
      //BLOCK_NONE?
      methodTreatmentContract.setSelection(props.getProperty(StrategyProperties.METHOD_OPTIONS_KEY).equals(StrategyProperties.METHOD_CONTRACT));
      methodTreatmentExpand.setSelection(props.getProperty(StrategyProperties.METHOD_OPTIONS_KEY).equals(StrategyProperties.METHOD_EXPAND));
      methodTreatmentNone.setSelection(props.getProperty(StrategyProperties.METHOD_OPTIONS_KEY).equals(StrategyProperties.METHOD_NONE));
      dependencyContratcsOn.setSelection(props.getProperty(StrategyProperties.DEP_OPTIONS_KEY).equals(StrategyProperties.DEP_ON));
      dependencyContratcsOff.setSelection(props.getProperty(StrategyProperties.DEP_OPTIONS_KEY).equals(StrategyProperties.DEP_OFF));
      queryTreatmentOn.setSelection(props.getProperty(StrategyProperties.QUERY_OPTIONS_KEY).equals(StrategyProperties.QUERY_ON));
      queryTreatmentRestricted.setSelection(props.getProperty(StrategyProperties.QUERY_OPTIONS_KEY).equals(StrategyProperties.QUERY_RESTRICTED));
      queryTreatmentOff.setSelection(props.getProperty(StrategyProperties.QUERY_OPTIONS_KEY).equals(StrategyProperties.QUERY_OFF));
      expandLocalQueriesOn.setSelection(props.getProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY).equals(StrategyProperties.QUERYAXIOM_ON));
      expandLocalQueriesOff.setSelection(props.getProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY).equals(StrategyProperties.QUERYAXIOM_OFF));
      arithmeticTreatmentBasic.setSelection(props.getProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY).equals(StrategyProperties.NON_LIN_ARITH_NONE));
      arithmeticTreatmentDefOps.setSelection(props.getProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY).equals(StrategyProperties.NON_LIN_ARITH_DEF_OPS));
      arithmeticTreatmentModelSearch.setSelection(props.getProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY).equals(StrategyProperties.NON_LIN_ARITH_COMPLETION));
      quantifierTreatmentNone.setSelection(props.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY).equals(StrategyProperties.QUANTIFIERS_NONE));
      quantifierTreatmentNoSplits.setSelection(props.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY).equals(StrategyProperties.QUANTIFIERS_NON_SPLITTING));
      quantifierTreatmentNoSplitsWithProgs.setSelection(props.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY).equals(StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS));
      quantifierTreatmentFree.setSelection(props.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY).equals(StrategyProperties.QUANTIFIERS_INSTANTIATE));
      autoInductionOn.setSelection(props.getProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY).equals(StrategyProperties.AUTO_INDUCTION_ON));
      autoInductionRestricted.setSelection(props.getProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY).equals(StrategyProperties.AUTO_INDUCTION_RESTRICTED));
      autoInductionOff.setSelection(props.getProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY).equals(StrategyProperties.AUTO_INDUCTION_OFF));
      //AUTO_INDUCTION_LEMMA_ON?
      userSpecificTacletsOneOff.setSelection(props.getProperty(StrategyProperties.USER_TACLETS_OPTIONS_KEY(1)).equals(StrategyProperties.USER_TACLETS_OFF));
      userSpecificTacletsOneLowPrior.setSelection(props.getProperty(StrategyProperties.USER_TACLETS_OPTIONS_KEY(1)).equals(StrategyProperties.USER_TACLETS_LOW));
      userSpecificTacletsOneHighPrior.setSelection(props.getProperty(StrategyProperties.USER_TACLETS_OPTIONS_KEY(1)).equals(StrategyProperties.USER_TACLETS_HIGH));
      userSpecificTacletsTwoOff.setSelection(props.getProperty(StrategyProperties.USER_TACLETS_OPTIONS_KEY(2)).equals(StrategyProperties.USER_TACLETS_OFF));
      userSpecificTacletsTwoLowPrior.setSelection(props.getProperty(StrategyProperties.USER_TACLETS_OPTIONS_KEY(2)).equals(StrategyProperties.USER_TACLETS_LOW));
      userSpecificTacletsTwoHighPrior.setSelection(props.getProperty(StrategyProperties.USER_TACLETS_OPTIONS_KEY(2)).equals(StrategyProperties.USER_TACLETS_HIGH));
      userSpecificTacletsThreeOff.setSelection(props.getProperty(StrategyProperties.USER_TACLETS_OPTIONS_KEY(3)).equals(StrategyProperties.USER_TACLETS_OFF));
      userSpecificTacletsThreeLowPrior.setSelection(props.getProperty(StrategyProperties.USER_TACLETS_OPTIONS_KEY(3)).equals(StrategyProperties.USER_TACLETS_LOW));
      userSpecificTacletsThreeHighPrior.setSelection(props.getProperty(StrategyProperties.USER_TACLETS_OPTIONS_KEY(3)).equals(StrategyProperties.USER_TACLETS_HIGH));
      
   }

   SelectionListener listener = new SelectionAdapter(){
      public void widgetSelected(SelectionEvent e){
          if(e.getSource().equals(stopAtDefault)&&stopAtDefault.getSelection()){
             props.put(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_DEFAULT);
          }
          else if(e.getSource().equals(stopAtUnclosable)&&stopAtUnclosable.getSelection()){
             props.put(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_NONCLOSE);
          }
          else if(e.getSource().equals(treatmentOfNewUnclosableGoalsNone)&&treatmentOfNewUnclosableGoalsNone.getSelection()){
             props.put(StrategyProperties.RETREAT_MODE_OPTIONS_KEY, StrategyProperties.RETREAT_MODE_NONE);
          }
          else if(e.getSource().equals(treatmentOfNewUnclosableGoalsAutoPrune)&&treatmentOfNewUnclosableGoalsAutoPrune.getSelection()){
             props.put(StrategyProperties.RETREAT_MODE_OPTIONS_KEY, StrategyProperties.RETREAT_MODE_RETREAT);
          }
          else if(e.getSource().equals(logicalSplittingDelayed)&&logicalSplittingDelayed.getSelection()){
             props.put(StrategyProperties.SPLITTING_OPTIONS_KEY, StrategyProperties.SPLITTING_DELAYED);
          }
          else if(e.getSource().equals(logicalSplittingFree)&&logicalSplittingFree.getSelection()){
             props.put(StrategyProperties.SPLITTING_OPTIONS_KEY, StrategyProperties.SPLITTING_NORMAL);
          }
          else if(e.getSource().equals(logicalSplittingOff)&&logicalSplittingOff.getSelection()){
             props.put(StrategyProperties.SPLITTING_OPTIONS_KEY, StrategyProperties.SPLITTING_OFF);
          }
          else if(e.getSource().equals(loopTreatmentInvariant)&&loopTreatmentInvariant.getSelection()){
             props.put(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_INVARIANT);
          }
          else if(e.getSource().equals(loopTreatmentExpand)&&loopTreatmentExpand.getSelection()){
             props.put(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_EXPAND);
          }
          else if(e.getSource().equals(loopTreatmentNone)&&loopTreatmentNone.getSelection()){
             props.put(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_NONE);
          }
          else if(e.getSource().equals(blockTreatmentContract)&&blockTreatmentContract.getSelection()){
             props.put(StrategyProperties.BLOCK_OPTIONS_KEY, StrategyProperties.BLOCK_CONTRACT);
          }
          else if(e.getSource().equals(blockTreatmentExpand)&&blockTreatmentExpand.getSelection()){
             props.put(StrategyProperties.BLOCK_OPTIONS_KEY, StrategyProperties.BLOCK_EXPAND);
          }
          else if(e.getSource().equals(methodTreatmentContract)&&methodTreatmentContract.getSelection()){
             props.put(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_CONTRACT);
          }
          else if(e.getSource().equals(methodTreatmentExpand)&&methodTreatmentExpand.getSelection()){
             props.put(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_EXPAND);
          }
          else if(e.getSource().equals(methodTreatmentNone)&&methodTreatmentNone.getSelection()){
             props.put(StrategyProperties.METHOD_OPTIONS_KEY, StrategyProperties.METHOD_NONE);
          }
          else if(e.getSource().equals(dependencyContratcsOn)&&dependencyContratcsOn.getSelection()){
             props.put(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_ON);
          }
          else if(e.getSource().equals(dependencyContratcsOff)&&dependencyContratcsOff.getSelection()){
             props.put(StrategyProperties.DEP_OPTIONS_KEY, StrategyProperties.DEP_OFF);
          }
          else if(e.getSource().equals(queryTreatmentOn)&&queryTreatmentOn.getSelection()){
             props.put(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_ON);
          }
          else if(e.getSource().equals(queryTreatmentRestricted)&&queryTreatmentRestricted.getSelection()){
             props.put(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_RESTRICTED);
          }
          else if(e.getSource().equals(queryTreatmentOff)&&queryTreatmentOff.getSelection()){
             props.put(StrategyProperties.QUERY_OPTIONS_KEY, StrategyProperties.QUERY_OFF);
          }
          else if(e.getSource().equals(expandLocalQueriesOn)&&expandLocalQueriesOn.getSelection()){
             props.put(StrategyProperties.QUERYAXIOM_OPTIONS_KEY, StrategyProperties.QUERYAXIOM_ON);
          }
          else if(e.getSource().equals(expandLocalQueriesOff)&&expandLocalQueriesOff.getSelection()){
             props.put(StrategyProperties.QUERYAXIOM_OPTIONS_KEY, StrategyProperties.QUERYAXIOM_OFF);
          }
          else if(e.getSource().equals(arithmeticTreatmentBasic)&&arithmeticTreatmentBasic.getSelection()){
             props.put(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_NONE);
          }
          else if(e.getSource().equals(arithmeticTreatmentDefOps)&&arithmeticTreatmentDefOps.getSelection()){
             props.put(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_DEF_OPS);
          }
          else if(e.getSource().equals(arithmeticTreatmentModelSearch)&&arithmeticTreatmentModelSearch.getSelection()){
             props.put(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, StrategyProperties.NON_LIN_ARITH_COMPLETION);
          }
          else if(e.getSource().equals(quantifierTreatmentNone)&&quantifierTreatmentNone.getSelection()){
             props.put(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NONE);
          }
          else if(e.getSource().equals(quantifierTreatmentNoSplits)&&quantifierTreatmentNoSplits.getSelection()){
             props.put(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NON_SPLITTING);
          }
          else if(e.getSource().equals(quantifierTreatmentNoSplitsWithProgs)&&quantifierTreatmentNoSplitsWithProgs.getSelection()){
             props.put(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
          }
          else if(e.getSource().equals(quantifierTreatmentFree)&&quantifierTreatmentFree.getSelection()){
             props.put(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_INSTANTIATE);
          }
          else if(e.getSource().equals(autoInductionOn)&&autoInductionOn.getSelection()){
             props.put(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY, StrategyProperties.AUTO_INDUCTION_ON);
          }
          else if(e.getSource().equals(autoInductionRestricted)&&autoInductionRestricted.getSelection()){
             props.put(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY, StrategyProperties.AUTO_INDUCTION_RESTRICTED);
          }
          else if(e.getSource().equals(autoInductionOff)&&autoInductionOff.getSelection()){
             props.put(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY, StrategyProperties.AUTO_INDUCTION_OFF);
          }
          else if(e.getSource().equals(userSpecificTacletsOneOff)&&userSpecificTacletsOneOff.getSelection()){
             props.put(StrategyProperties.USER_TACLETS_OPTIONS_KEY(1), StrategyProperties.USER_TACLETS_OFF);
          }
          else if(e.getSource().equals(userSpecificTacletsOneLowPrior)&&userSpecificTacletsOneLowPrior.getSelection()){
             props.put(StrategyProperties.USER_TACLETS_OPTIONS_KEY(1), StrategyProperties.USER_TACLETS_LOW);
          }
          else if(e.getSource().equals(userSpecificTacletsOneHighPrior)&&userSpecificTacletsOneHighPrior.getSelection()){
             props.put(StrategyProperties.USER_TACLETS_OPTIONS_KEY(1), StrategyProperties.USER_TACLETS_HIGH);
          }
          else if(e.getSource().equals(userSpecificTacletsTwoOff)&&userSpecificTacletsTwoOff.getSelection()){
             props.put(StrategyProperties.USER_TACLETS_OPTIONS_KEY(2), StrategyProperties.USER_TACLETS_OFF);
          }
          else if(e.getSource().equals(userSpecificTacletsTwoLowPrior)&&userSpecificTacletsTwoLowPrior.getSelection()){
             props.put(StrategyProperties.USER_TACLETS_OPTIONS_KEY(2), StrategyProperties.USER_TACLETS_LOW);
          }
          else if(e.getSource().equals(userSpecificTacletsTwoHighPrior)&&userSpecificTacletsTwoHighPrior.getSelection()){
             props.put(StrategyProperties.USER_TACLETS_OPTIONS_KEY(2), StrategyProperties.USER_TACLETS_HIGH);
          }
          else if(e.getSource().equals(userSpecificTacletsThreeOff)&&userSpecificTacletsThreeOff.getSelection()){
             props.put(StrategyProperties.USER_TACLETS_OPTIONS_KEY(3), StrategyProperties.USER_TACLETS_OFF);
          }
          else if(e.getSource().equals(userSpecificTacletsThreeLowPrior)&&userSpecificTacletsThreeLowPrior.getSelection()){
             props.put(StrategyProperties.USER_TACLETS_OPTIONS_KEY(3), StrategyProperties.USER_TACLETS_LOW);
          }
          else if(e.getSource().equals(userSpecificTacletsThreeHighPrior)&&userSpecificTacletsThreeHighPrior.getSelection()){
             props.put(StrategyProperties.USER_TACLETS_OPTIONS_KEY(3), StrategyProperties.USER_TACLETS_HIGH);
          }
          proof.getSettings().getStrategySettings().setActiveStrategyProperties(props);
      }
   };
   
   ModifyListener maxStepListener = new ModifyListener(){
      @Override
      public void modifyText(ModifyEvent e) {
         if(e.getSource() instanceof Text){
            boolean firstValueZero = true;
            Text text = (Text)e.getSource();
            String string = text.getText();
            char [] chars = new char [string.length ()];
            string.getChars (0, chars.length, chars, 0);
            if(text.getText()==""){
               return;
            }
            for (int i=0; i<chars.length; i++) {
               if (!('0' <= chars [i] && chars [i] <= '9')) {
                  text.setText("");
                  return;
               } 
            }
            
            int steps = Integer.parseInt(string);
            if(steps<1){
               steps=1;
               text.setText(String.valueOf(steps));
               return;
            }
            if(steps>1000000){
               steps=1000000;
               text.setText(String.valueOf(steps));
               return;
            }
            for (int i=0; i<chars.length; i++) {
               if( chars[i] == '0' && firstValueZero){
                  text.setText(String.valueOf(chars, i+1,  chars.length-i-1));
                  return;
               }else{
                  firstValueZero = false;
               }
            }
            proof.getSettings().getStrategySettings().setMaxSteps(steps);
         }
      }
      
   };
   
   
}