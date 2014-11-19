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

package org.key_project.key4eclipse.common.ui.decorator;

import java.io.IOException;

import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.JFaceTextUtil;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseMoveListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.ui.services.IDisposable;
import org.key_project.util.bean.Bean;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.GenericSortInstantiations;

/**
 * The Decorator for the KeYEditor.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class ProofSourceViewerDecorator extends Bean implements IDisposable {
   /**
    * Property {@link #getSelectedPosInSequent()}.
    */
   public static final String PROP_SELECTED_POS_IN_SEQUENT = "selectedPosInSequent";
   
   /**
    * The {@link ISourceViewer} to decorate.
    */
   private final ISourceViewer viewer;
   
   /**
    * The {@link StyledText} provided by {@link #viewer} via {@link ISourceViewer#getTextWidget()}.
    */
   private final StyledText viewerText;
   
   /**
    * The currently shown node.
    */
   private Node node;

   /**
    * The {@link SequentPrintFilter} used to compute the shown text in {@link #viewer}.
    */
   private SequentPrintFilter filter;
   
   /**
    * The {@link LogicPrinter} used to compute the shown text in {@link #viewer}.
    */
   private LogicPrinter printer;
   
   /**
    * The {@link TextPresentation} shown in {@link #viewerText}.
    */
   private TextPresentation textPresentation;
   
   /**
    * The first range used to highlight the selected {@link Term}.
    */
   private StyleRange marked1;
   
   /**
    * The second range used to highlight the selected {@link Term}.
    */
   private StyleRange marked2;
   
   /**
    * The {@link StyleRange} to highlight the active statement.
    */
   private StyleRange firstStatementStyleRange;
   
   /**
    * The currently selected {@link PosInSequent}.
    */
   private PosInSequent selectedPosInSequent;
   
   /**
    * Listens for mouse move events on {@link #viewerText}.
    */
   private MouseMoveListener mouseMoveListener = new MouseMoveListener(){
      @Override
      public void mouseMove(MouseEvent e) {
         handleMouseMoved(e);
      }
   };

   /**
    * Constructor.
    * @param viewer The {@link ISourceViewer} to decorate.
    */
   public ProofSourceViewerDecorator(ISourceViewer viewer) {
      this.viewer = viewer;
      this.viewerText = viewer.getTextWidget();
      this.viewerText.addMouseMoveListener(mouseMoveListener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (viewerText != null && !viewerText.isDisposed()) {
         viewerText.removeMouseMoveListener(mouseMoveListener);
      }
   }
   
   /**
    * Shows the given {@link Node} with help of the given {@link KeYMediator}
    * in the decorated {@link ISourceViewer}.
    * @param node The {@link Node} to show.
    * @param mediator The {@link KeYMediator} to use.
    */
   public void showNode(Node node, KeYMediator mediator) {
      this.node = node;
      String str;
      if (node != null) {
         filter = new IdentitySequentPrintFilter(node.sequent());
         printer = new LogicPrinter(new ProgramPrinter(null), 
                                    mediator.getNotationInfo(), 
                                    node.proof().getServices());
         str = computeText(mediator, node, filter, printer);
      }
      else {
         filter = null;
         printer = null;
         str = "";
      }
      viewer.setDocument(new Document(str));
      if (node != null && node.getAppliedRuleApp() != null) {
         PosInOccurrence pio = node.getAppliedRuleApp().posInOccurrence();
         setGreenBackground(pio);
      }
   }
   
   /**
    * Shows the given {@link Term} with help of the given {@link KeYMediator}
    * in the decorated {@link ISourceViewer}.
    * @param term The {@link Term} to show.
    * @param services The {@link Services} to use.
    * @param mediator The {@link KeYMediator} to use.
    * @param visibleLabels Optional definition of visible {@link TermLabel}s.
    * @return The shown text.
    */
   public String showTerm(Term term, 
                          Services services, 
                          KeYMediator mediator, 
                          VisibleTermLabels visibleLabels) {
      this.node = null;
      filter = null;
      if (visibleLabels != null) {
         printer = new SequentViewLogicPrinter(new ProgramPrinter(null), 
                                               mediator.getNotationInfo(), 
                                               services,
                                               visibleLabels);
      }
      else {
         printer = new LogicPrinter(new ProgramPrinter(null), 
                                    mediator.getNotationInfo(), 
                                    services);
      }
      String str = computeText(mediator, term, printer);
      viewer.setDocument(new Document(str));
      return str;
   }
   
   /**
    * Computes the text to show in the {@link KeYEditor}} which consists
    * of the sequent including the applied rule.
    * @param mediator The {@link KeYMediator} to use.
    * @param node The {@link Node} to use.
    * @param filter The {@link SequentPrintFilter} to use.
    * @param printer The {@link LogicPrinter} to use.
    * @return The text to show.
    */
   public static String computeText(KeYMediator mediator, 
                                    Term term, 
                                    LogicPrinter printer) {
      try {
         printer.printTerm(term);
         String s = printer.toString();
         return StringUtil.trimRight(s);
      }
      catch (IOException e) {
         return e.getMessage();
      }
   }
   
   /**
    * Computes the text to show in the {@link KeYEditor}} which consists
    * of the sequent including the applied rule.
    * @param mediator The {@link KeYMediator} to use.
    * @param node The {@link Node} to use.
    * @param filter The {@link SequentPrintFilter} to use.
    * @param printer The {@link LogicPrinter} to use.
    * @return The text to show.
    */
   public static String computeText(KeYMediator mediator, 
                                    Node node, 
                                    SequentPrintFilter filter, 
                                    LogicPrinter printer) {
      
      printer.printSequent(filter);
      String s = printer.toString();
      RuleApp app = node.getAppliedRuleApp();
      s += "\nNode Nr " + node.serialNr() + "\n";
      s += ruleToString(mediator, app, true);
      return s;
   }
   
   public static String ruleToString(KeYMediator mediator, RuleApp app, boolean withHeadder) {
      String s = StringUtil.EMPTY_STRING;
      if ( app != null ) {
         if (withHeadder) {
            s = s + "\n \nUpcoming rule application: \n";
         }
         if (app.rule() instanceof Taclet) {
        LogicPrinter tacPrinter = new LogicPrinter 
            (new ProgramPrinter(null),                        
             mediator.getNotationInfo(),
             mediator.getServices(),
             true);  
        tacPrinter.printTaclet((Taclet)(app.rule()));    
        s += tacPrinter;
         } else {
           s = s + app.rule();
         }

         if ( app instanceof TacletApp ) {
        TacletApp tapp = (TacletApp)app;
        if ( tapp.instantiations ().getGenericSortInstantiations () !=
             GenericSortInstantiations.EMPTY_INSTANTIATIONS ) {
            s = s + "\n\nWith sorts:\n";
            s = s +
           tapp.instantiations ().getGenericSortInstantiations ();
        }
         }        
     }
      return s;
   }
   
   protected void setGreenBackground(PosInOccurrence pos){
      initializeValuesForGreenBackground();
      if (pos != null) {
         ImmutableList<Integer> path = printer.getInitialPositionTable().pathForPosition(pos, filter);
         Range range = printer.getInitialPositionTable().rangeForPath(path);
         marked1.start = range.start();
         marked1.length = range.end()-range.start();
         TextPresentation.applyTextPresentation(textPresentation, viewerText);
         viewer.changeTextPresentation(textPresentation, true);
      }
   }
   
   protected void initializeValuesForGreenBackground(){
      marked1 = new StyleRange();
      marked1.background=new Color(null,128,255,128);    
      textPresentation = new TextPresentation();
      textPresentation.addStyleRange(marked1);
      viewer.changeTextPresentation(textPresentation, true);
   }

   /**
    * Handles a mouse move event on {@link #viewerText}.
    * @param e The event.
    */
   protected void handleMouseMoved(MouseEvent e) {
      if (node != null) {
         // Update selected PosInSequent
         PosInSequent oldPos = selectedPosInSequent;
         int textOffset = JFaceTextUtil.getOffsetForCursorLocation(viewer);
         if (textOffset >= 0) {
            selectedPosInSequent = printer.getInitialPositionTable().getPosInSequent(textOffset, filter);
         }
         else {
            selectedPosInSequent = null;
         }
         // Update shown highlighting if PosInSequent has changed
         if (!ObjectUtil.equals(oldPos, selectedPosInSequent)) {
            // Update highlighting only on goals.
            if (node.getAppliedRuleApp() == null){
               setBackgroundColorForHover();
            }
            // Inform listener
            firePropertyChange(PROP_SELECTED_POS_IN_SEQUENT, oldPos, selectedPosInSequent);
         }
      }
   }

   protected void setBackgroundColorForHover(){
      initializeValuesForHover();
      
      int textOffset = JFaceTextUtil.getOffsetForCursorLocation(viewer);
      Range range = printer.getInitialPositionTable().rangeForIndex(textOffset);
      Range firstStatement = printer.getPositionTable().firstStatementRangeForIndex(textOffset);
      
      if(firstStatement != null){
         firstStatementStyleRange.start = firstStatement.start();
         firstStatementStyleRange.length = firstStatement.end()-firstStatement.start();
      
         //start vor first
         if(range.start() < firstStatement.start()){
            //ende vor first 
            if(range.end() < firstStatement.start()){
               marked1.start = range.start();
               marked1.length = range.length();
            }
            //ende in first
            else if(range.end() >= firstStatement.start() && range.end() <= firstStatement.end()){
               marked1.start = range.start();
               marked1.length = (firstStatement.start()) - range.start();
            }
            //ende nach first
            else if(range.end() > firstStatement.end()){
               marked1.start = range.start();
               marked1.length = (firstStatement.start()) - range.start();
               marked2.start = firstStatement.end();
               marked2.length = range.end() - (firstStatement.end());
            }
         }
         //start in first
         else if(range.start() >= firstStatement.start() && range.start() <= firstStatement.end()){
            //ende nach first
            if(range.end() > firstStatement.end()){
               marked1.start = firstStatement.end();
               marked1.length = range.end() - (firstStatement.end());
            }
         }
         //start nach first
         else if(range.start() > firstStatement.end()){
            marked1.start = range.start();
            marked1.length = range.length();
         }
      }
      else {
         marked1.start = range.start();
         marked1.length = range.length(); 
      }
      StyleRange[] ranges = {marked1, marked2, firstStatementStyleRange};
      textPresentation.mergeStyleRanges(ranges);
//      textPresentation.addStyleRange(firstStatementStyleRange);
      TextPresentation.applyTextPresentation(textPresentation, viewerText);
      viewer.changeTextPresentation(textPresentation, true);
   }
   
   protected void initializeValuesForHover(){
      marked1 = new StyleRange();
      marked1.background=new Color(null,196,205,226);
      marked2 = new StyleRange();
      marked2.background=new Color(null,196,205,226);
      firstStatementStyleRange = new StyleRange();
      firstStatementStyleRange.background = new Color(null, 167,174,192);
      textPresentation = new TextPresentation();
//      textPresentation.addStyleRange(marked1);
//      textPresentation.mergeStyleRange(firstStatementStyleRange);
      viewer.changeTextPresentation(textPresentation, true);
   }

   /**
    * Returns the selected {@link PosInSequent} for the current cursor location.
    * @return The selected {@link PosInSequent} for the current cursor location.
    */
   public PosInSequent getSelectedPosInSequent() {
      return selectedPosInSequent;
   }

   /**
    * Returns the used {@link LogicPrinter}.
    * @return The used {@link LogicPrinter}.
    */
   protected LogicPrinter getPrinter() {
      return printer;
   }

   /**
    * Returns the {@link ISourceViewer} in which this decorator is used.
    * @return The {@link ISourceViewer} in which this decorator is used.
    */
   protected ISourceViewer getViewer() {
      return viewer;
   }

   /**
    * Returns the {@link StyledText} of {@link #getViewer()}.
    * @return The {@link StyledText} of {@link #getViewer()}.
    */
   protected StyledText getViewerText() {
      return viewerText;
   }
}