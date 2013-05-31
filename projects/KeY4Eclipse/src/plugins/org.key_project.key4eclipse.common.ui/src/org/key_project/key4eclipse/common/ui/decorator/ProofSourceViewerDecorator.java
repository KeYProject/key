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

package org.key_project.key4eclipse.common.ui.decorator;

import java.util.Iterator;

import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.JFaceTextUtil;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Color;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.GenericSortInstantiations;

/**
 * The Decorator for the KeYEditor.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class ProofSourceViewerDecorator {
   // TODO: Document missing members of class ProofSourceViewerDecorator

   private SequentPrintFilter filter;
   
   private LogicPrinter printer;
   
   private StyleRange marked1;
   
   private StyleRange marked2;
   
   private StyleRange firstStatementStyleRange;
   
   private TextPresentation textPresentation;
   
   private ISourceViewer viewer;
   
   public ISourceViewer getISourceViewer(){
      return this.viewer;
   }

   public ProofSourceViewerDecorator(ISourceViewer viewer) {
      this.viewer = viewer;
   }
   
   private void initializeValuesForHover(){
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
   
   private void initializeValuesForGreenBackground(){
      marked1 = new StyleRange();
      marked1.background=new Color(null,128,255,128);    
      textPresentation = new TextPresentation();
      textPresentation.addStyleRange(marked1);
      viewer.changeTextPresentation(textPresentation, true);
      
   }
   
   public void setDocumentForNode(Node node, KeYMediator mediator){
      filter = new IdentitySequentPrintFilter(node.sequent());
      printer = new LogicPrinter(new ProgramPrinter(null), 
                                              mediator.getNotationInfo(), 
                                              node.proof().getServices());
      String str = computeText(mediator, node, filter, printer);
      viewer.setDocument(new Document(str));
   }

   @SuppressWarnings("static-access")
   public void setBackgroundColorForHover(){
      initializeValuesForHover();
      
      int textOffset = JFaceTextUtil.getOffsetForCursorLocation(viewer);
      Range range = printer.getPositionTable().rangeForIndex(textOffset);
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
      textPresentation.applyTextPresentation(textPresentation, viewer.getTextWidget());
      viewer.changeTextPresentation(textPresentation, true);
   }
   
   @SuppressWarnings("static-access")
   public void setGreenBackground(PosInOccurrence pos){
      initializeValuesForGreenBackground();
      ImmutableList<Integer> path = printer.getPositionTable().pathForPosition(pos, filter);
      Range range = printer.getPositionTable().rangeForPath(path);
      marked1.start = range.start();
      marked1.length = range.end()-range.start();
      textPresentation.applyTextPresentation(textPresentation, viewer.getTextWidget());
      viewer.changeTextPresentation(textPresentation, true);
   }
   
   
   /**
    * <p>
    * Computes the text to show in the {@link KeYEditor}} which consists
    * of the sequent including the applied rule.
    * </p>
    * <p>
    * This information is also relevant for other tools like the
    * Symbolic Execution Debugger.
    * </p>
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
      
        printer.printSequent (null, filter);
        String s = printer.toString();
             printer=null;
        RuleApp app = node.getAppliedRuleApp();
             s += "\nNode Nr "+node.serialNr()+"\n";
             
        if ( app != null ) {
            s = s + "\n \nUpcoming rule application: \n";
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

           StringBuffer sb = new StringBuffer("\n\n");
           s = s + sb;
            }        
        }
        return s;
   }
   
   
   /**
    * Returns the {@link PosInSequent} for the current cursor location.
    * @return PosInSequent - the {@link PosInSequent} for the current cursor location.
    */
   public PosInSequent getPosInSequent(){
      int textOffset = JFaceTextUtil.getOffsetForCursorLocation(viewer);
      if(textOffset >= 0){
         return printer.getPositionTable().getPosInSequent(textOffset, filter);
      }
      else return null;
   }
   
   
   /**
    * Collects all applicable {@link TacletApp}s for a given {@link PosInSequent} and {@link KeYMediator}.
    * @param mediator - the {@link KeYMediator} of the current {@link Proof}.
    * @param pos - the {@link PosInSequent} to find the {@link TacletApp}s for.
    * @return {@link ImmutableList} - the {@link ImmutableList} with all applicable {@link TacletApp}s.
    */
   public ImmutableList<TacletApp> findRules(KeYMediator mediator, PosInSequent pos){
      if(pos != null){
         ImmutableList<TacletApp> findTacletList = mediator.getFindTaclet(pos);
         ImmutableList<TacletApp> reWriteTacletList = mediator.getRewriteTaclet(pos);
         ImmutableList<TacletApp> noFindTacletList = mediator.getNoFindTaclet();
         
         findTacletList = removeObsolete(findTacletList);
         reWriteTacletList = removeObsolete(reWriteTacletList);
         noFindTacletList = removeObsolete(noFindTacletList);
         
         ImmutableList<TacletApp> allTaclets = removeRewrites(findTacletList).prepend(reWriteTacletList);
         
         return allTaclets;
      }
      else{ 
         return null;
      }
   }
      
   
   /** Remove rules which belong to rule set "obsolete".
    * Obsolete rules are sound, but are discouraged to use in
    * both automated and interactive proofs, mostly because of proof complexity issues.
    */
   private ImmutableList<TacletApp> removeObsolete(ImmutableList<TacletApp> list) {
       ImmutableList<TacletApp> result = ImmutableSLList.<TacletApp>nil();
       for (TacletApp ta: list) {
           boolean isObsolete = false;
           for (RuleSet rs: ta.taclet().getRuleSets()) {
               if (rs.name().equals(new Name("obsolete"))) {
                   isObsolete = true;
                   break;
               }
           }
           if (!isObsolete)
               result = result.append(ta);
       }
       return result;
   }
   
   
   /** removes RewriteTaclet from list
    * @param list the IList<Taclet> from where the RewriteTaclet are
    * removed
    * @return list without RewriteTaclets
    */
   private ImmutableList<TacletApp> removeRewrites(ImmutableList<TacletApp> list) {
  ImmutableList<TacletApp> result = ImmutableSLList.<TacletApp>nil();
  Iterator<TacletApp> it = list.iterator();

  while(it.hasNext()) {
      TacletApp tacletApp = it.next();
      Taclet taclet=tacletApp.taclet();
      result = (taclet instanceof RewriteTaclet ? result :
           result.prepend(tacletApp));
  }
  return result;
   }
   
}
