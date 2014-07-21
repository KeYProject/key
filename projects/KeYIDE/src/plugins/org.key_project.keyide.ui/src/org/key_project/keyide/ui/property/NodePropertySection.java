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

package org.key_project.keyide.ui.property;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.views.properties.tabbed.AbstractPropertySection;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.key4eclipse.common.ui.decorator.ProofSourceViewerDecorator;
import org.key_project.keyide.ui.providers.ProofTreeLabelProvider;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.proof.Node;

/**
 * This {@link AbstractPropertySection} shows the content of a {@link Node}.
 * @author Martin Hentschel
 */
public class NodePropertySection extends AbstractNodePropertySection {
   /**
    * Shows the name.
    */
   private Text nameText;

   /**
    * Shows the applied rule.
    */
   private Text appliedRuleText;
   
   /**
    * Indicates that the {@link Node} is closed.
    */
   private Button closedButton;
   
   /**
    * Indicates the rule was applied interactively.
    */
   private Button interactiveRuleButton;

   /**
    * The first statement.
    */
   private Text firstStatementText;

   /**
    * The active statement.
    */
   private Text activeStatementText;

   /**
    * The active statement parent class.
    */
   private Text activeStatementParentClassText;

   /**
    * The active statement position.
    */
   private Text activeStatementPositionText;

   /**
    * The counted branches.
    */
   private Text branchesText;

   /**
    * The counted nodes.
    */
   private Text nodesText;
   
   /**
    * The global program variables.
    */
   private List globalProgVarList;
   
   /**
    * The introduced rules.
    */
   private List introducedRulesList;
   
   /**
    * The used renamings.
    */
   private List renamingsList;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControls(Composite parent, TabbedPropertySheetPage tabbedPropertySheetPage) {
      super.createControls(parent, tabbedPropertySheetPage);
      TabbedPropertySheetWidgetFactory factory = getWidgetFactory();
      
      Composite composite = factory.createFlatFormComposite(parent);

      nameText = factory.createText(composite, StringUtil.EMPTY_STRING);
      addControlRow(factory, composite, null, nameText, "Name: ");

      appliedRuleText = factory.createText(composite, StringUtil.EMPTY_STRING, SWT.MULTI);
      addControlRow(factory, composite, nameText, appliedRuleText, "Applied Rule: ");

      interactiveRuleButton = factory.createButton(composite, StringUtil.EMPTY_STRING, SWT.CHECK);
      addControlRow(factory, composite, appliedRuleText, interactiveRuleButton, "Interactive Rule Application: ");
      
      closedButton = factory.createButton(composite, StringUtil.EMPTY_STRING, SWT.CHECK);
      addControlRow(factory, composite, interactiveRuleButton, closedButton, "Closed: ");

      firstStatementText = factory.createText(composite, StringUtil.EMPTY_STRING);
      addControlRow(factory, composite, closedButton, firstStatementText, "First Statement: ");

      activeStatementText = factory.createText(composite, StringUtil.EMPTY_STRING);
      addControlRow(factory, composite, firstStatementText, activeStatementText, "Active Statement: ");

      activeStatementParentClassText = factory.createText(composite, StringUtil.EMPTY_STRING);
      addControlRow(factory, composite, activeStatementText, activeStatementParentClassText, "Active Statement Class: ");

      activeStatementPositionText = factory.createText(composite, StringUtil.EMPTY_STRING);
      addControlRow(factory, composite, activeStatementParentClassText, activeStatementPositionText, "Active Statement Position: ");

      branchesText = factory.createText(composite, StringUtil.EMPTY_STRING);
      addControlRow(factory, composite, activeStatementPositionText, branchesText, "Branches Count: ");

      nodesText = factory.createText(composite, StringUtil.EMPTY_STRING);
      addControlRow(factory, composite, branchesText, nodesText, "Nodes Count: ");
      
      globalProgVarList = factory.createList(composite, SWT.BORDER | SWT.MULTI);
      addControlRow(factory, composite, nodesText, globalProgVarList, "Global Program Variables: ");
      
      introducedRulesList = factory.createList(composite, SWT.BORDER | SWT.MULTI);
      addControlRow(factory, composite, globalProgVarList, introducedRulesList, "Introduced Rules: ");
      
      renamingsList = factory.createList(composite, SWT.BORDER | SWT.MULTI);
      addControlRow(factory, composite, introducedRulesList, renamingsList, "Renaming Tables: ");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void updateShownContent(KeYMediator mediator, Node node) {
      if (node != null) {
         SWTUtil.setText(nameText, ProofTreeLabelProvider.getNodeText(node));
         SWTUtil.setText(appliedRuleText, ProofSourceViewerDecorator.ruleToString(mediator, node.getAppliedRuleApp(), false));
         interactiveRuleButton.setSelection(node.getNodeInfo().getInteractiveRuleApplication());
         closedButton.setSelection(node.isClosed());
         SWTUtil.setText(firstStatementText, node.getNodeInfo().getFirstStatementString());
         SWTUtil.setText(activeStatementText, ObjectUtil.toString(node.getNodeInfo().getActiveStatement()));
         SWTUtil.setText(activeStatementParentClassText, ObjectUtil.toString(node.getNodeInfo().getExecStatementParentClass()));
         SWTUtil.setText(activeStatementPositionText, ObjectUtil.toString(node.getNodeInfo().getExecStatementPosition()));
         SWTUtil.setText(branchesText, ObjectUtil.toString(node.countBranches()));
         SWTUtil.setText(nodesText, ObjectUtil.toString(node.countNodes()));

         setListValues(globalProgVarList, node.getGlobalProgVars());
         
         setListValues(introducedRulesList, node.getLocalIntroducedRules());
         
         setListValues(renamingsList, node.getRenamingTable());
      }
      else {
         nameText.setText(StringUtil.EMPTY_STRING);
         appliedRuleText.setText(StringUtil.EMPTY_STRING);
         interactiveRuleButton.setSelection(false);
         closedButton.setSelection(false);
         firstStatementText.setText(StringUtil.EMPTY_STRING);
         activeStatementText.setText(StringUtil.EMPTY_STRING);
         activeStatementParentClassText.setText(StringUtil.EMPTY_STRING);
         activeStatementPositionText.setText(StringUtil.EMPTY_STRING);
         branchesText.setText(StringUtil.EMPTY_STRING);
         nodesText.setText(StringUtil.EMPTY_STRING);
         globalProgVarList.removeAll();
         introducedRulesList.removeAll();
         renamingsList.removeAll();
      }
   }
}