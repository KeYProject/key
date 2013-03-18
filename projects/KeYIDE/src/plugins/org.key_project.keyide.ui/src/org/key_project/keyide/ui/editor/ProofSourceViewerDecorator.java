package org.key_project.keyide.ui.editor;

import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.JFaceTextUtil;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Color;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.GenericSortInstantiations;

public class ProofSourceViewerDecorator {

   private SequentPrintFilter filter;
   
   private LogicPrinter printer;
   
   private StyleRange marked;
   
   private StyleRange firstStatementStyleRange;
   
   private TextPresentation textPresentation;
   
   private ISourceViewer viewer;

   public ProofSourceViewerDecorator(ISourceViewer viewer) {
      this.viewer = viewer;
      initializeValues();
   }
   
   private void initializeValues(){
      marked = new StyleRange();
      marked.background=new Color(null,200,200,200);
      firstStatementStyleRange = new StyleRange();
      firstStatementStyleRange.background = new Color(null, 50,50,50);
      textPresentation = new TextPresentation();
      textPresentation.addStyleRange(marked);
      textPresentation.mergeStyleRange(firstStatementStyleRange);
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
      
      int textOffset = JFaceTextUtil.getOffsetForCursorLocation(viewer);
      Range range = printer.getPositionTable().rangeForIndex(textOffset);
      marked.start = range.start();
      marked.length = range.end()-range.start();
      
      Range firstStatement = printer.getPositionTable().firstStatementRangeForIndex(textOffset);
      if(firstStatement != null){
         firstStatementStyleRange.start = firstStatement.start();
         firstStatementStyleRange.length = firstStatement.end()-firstStatement.start();
      }

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
}
