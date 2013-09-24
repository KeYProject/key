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

package org.key_project.sed.key.ui.property;

import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CLabel;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.views.properties.tabbed.AbstractPropertySection;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertyConstants;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.key4eclipse.common.ui.decorator.ProofSourceViewerDecorator;
import org.key_project.sed.key.core.model.IKeYSEDDebugNode;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.Node;

/**
 * This composite provides the content shown in {@link KeYDebugNodePropertySection}
 * and {@link KeYGraphitiDebugNodePropertySection}.
 * @author Martin Hentschel
 */
public class KeYTabComposite extends Composite {
   /**
    * Shows the node id with applied rule of the node in KeY's proof tree represented by the current {@link IKeYSEDDebugNode}.
    */
   private Text nodeText;
   
   /**
    * Shows the {@link Sequent} of the node in KeY's proof tree represented by the current {@link IKeYSEDDebugNode}.
    */
   private SourceViewer sequentViewer;
   
   /**
    * The {@link ProofSourceViewerDecorator} used to decorate {@link #sequentViewer}.
    */
   private ProofSourceViewerDecorator sequentViewerDecorator;
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style to use.
    * @param factory The {@link TabbedPropertySheetWidgetFactory} to use.
    */
   public KeYTabComposite(Composite parent, int style, TabbedPropertySheetWidgetFactory factory) {
      super(parent, style);
      setLayout(new FillLayout());
      
      Composite composite = factory.createFlatFormComposite(this);

      nodeText = factory.createText(composite, StringUtil.EMPTY_STRING);
      nodeText.setEditable(false);
      FormData data = new FormData();
      data.left = new FormAttachment(0, AbstractPropertySection.STANDARD_LABEL_WIDTH);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(0, ITabbedPropertyConstants.VSPACE);
      nodeText.setLayoutData(data);

      CLabel nodeLabel = factory.createCLabel(composite, "Node:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(nodeText, -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(nodeText, 0, SWT.CENTER);
      nodeLabel.setLayoutData(data);

      sequentViewer = new SourceViewer(composite, null, SWT.MULTI | SWT.BORDER | SWT.FULL_SELECTION);
      sequentViewer.setEditable(false);
      data = new FormData();
      data.left = new FormAttachment(0, AbstractPropertySection.STANDARD_LABEL_WIDTH);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(nodeText, 0, ITabbedPropertyConstants.VSPACE);
      sequentViewer.getControl().setLayoutData(data);
      sequentViewerDecorator = new ProofSourceViewerDecorator(sequentViewer);
      
      CLabel sequentLabel = factory.createCLabel(composite, "Sequent:");
      data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(sequentViewer.getControl(), -ITabbedPropertyConstants.HSPACE);
      data.top = new FormAttachment(sequentViewer.getControl(), 0, SWT.TOP);
      sequentLabel.setLayoutData(data);
   }
   
   /**
    * Updates the shown content.
    * @param node The {@link IKeYSEDDebugNode} which provides the new content.
    */
   public void updateContent(IKeYSEDDebugNode<?> node) {
      String name = null;
      Node keyNode = null;
      KeYMediator mediator = null;
      if (node != null) {
         keyNode = node.getExecutionNode().getProofNode();
         mediator = node.getExecutionNode().getMediator();
         name = keyNode.serialNr() + ": " + keyNode.name(); // Copied from ProofRenderer
      }
      SWTUtil.setText(nodeText, name);
      sequentViewerDecorator.showNode(keyNode, mediator);
   }
}