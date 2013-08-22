package org.key_project.keyide.ui.property;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.List;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Node;

/**
 * Shows the current {@link PosInSequent} and the selected {@link Term}.
 * @author Martin Hentschel
 */
public class TermPropertySection extends AbstractNodePropertySection {
   /**
    * The observed {@link KeYEditor} which provides the {@link PosInSequent}.
    */
   private KeYEditor editor;
   
   /**
    * The listener to observe {@link #editor}.
    */
   private PropertyChangeListener listener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         updateShownContentThreadSave();
      }
   };

   /**
    * Shows {@link PosInSequent}.
    */
   private Text pioText;

   /**
    * Shows {@link Term#sort()}.
    */
   private Text sortText;

   /**
    * Shows the {@link Term#op()}.
    */
   private Text opText;
   
   /**
    * Shows the {@link Term#subs()}.
    */
   private List subsList;

   /**
    * Shows the {@link Term#freeVars()}.
    */
   private List freeVarsList;

   /**
    * Shows the {@link Term#boundVars()}.
    */
   private List boundVarsList;
   
   /**
    * Shows the {@link Term#javaBlock()}.
    */
   private Text javaBlockText;
   
   /**
    * Shows the {@link Term#getLabels()}.
    */
   private List labelList;

   /**
    * Shows the {@link Term#hashCode()}.
    */
   private Text hashCodeText;

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControls(Composite parent, TabbedPropertySheetPage tabbedPropertySheetPage) {
      super.createControls(parent, tabbedPropertySheetPage);
      TabbedPropertySheetWidgetFactory factory = getWidgetFactory();
      
      Composite composite = factory.createFlatFormComposite(parent);

      pioText = factory.createText(composite, StringUtil.EMPTY_STRING);
      addControlRow(factory, composite, null, pioText, "Position: ");

      sortText = factory.createText(composite, StringUtil.EMPTY_STRING);
      addControlRow(factory, composite, pioText, sortText, "Sort: ");

      opText = factory.createText(composite, StringUtil.EMPTY_STRING);
      addControlRow(factory, composite, sortText, opText, "Operator: ");

      subsList = factory.createList(composite, SWT.BORDER | SWT.MULTI);
      addControlRow(factory, composite, opText, subsList, "Children: ");

      freeVarsList = factory.createList(composite, SWT.BORDER | SWT.MULTI);
      addControlRow(factory, composite, subsList, freeVarsList, "Free Variables: ");

      boundVarsList = factory.createList(composite, SWT.BORDER | SWT.MULTI);
      addControlRow(factory, composite, freeVarsList, boundVarsList, "Bound Variables: ");

      javaBlockText = factory.createText(composite, StringUtil.EMPTY_STRING, SWT.MULTI);
      addControlRow(factory, composite, boundVarsList, javaBlockText, "Java Block: ");

      labelList = factory.createList(composite, SWT.BORDER | SWT.MULTI);
      addControlRow(factory, composite, javaBlockText, labelList, "Label: ");

      hashCodeText = factory.createText(composite, StringUtil.EMPTY_STRING);
      addControlRow(factory, composite, labelList, hashCodeText, "Hash Code: ");
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void setInput(IWorkbenchPart part, ISelection selection) {
      if (editor != null) {
         editor.removePropertyChangeListener(listener);
         editor = null;
      }
      part = updatePart(part);
      if (part instanceof KeYEditor) {
         editor = (KeYEditor)part;
         editor.addPropertyChangeListener(listener);
      }
      super.setInput(part, selection);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void updateShownContent(KeYMediator mediator, Node node) {
      // Show position
      PosInSequent pis = editor != null ? editor.getSelectedPosInSequent() : null;
      pioText.setText(posInSequentToString(pis));
      // Show term information
      Term term = pis != null && pis.getPosInOccurrence() != null ? pis.getPosInOccurrence().subTerm() : null;
      if (term != null) {
         SWTUtil.setText(sortText, ObjectUtil.toString(term.sort()));
         SWTUtil.setText(opText, operatorToString(term.op()));
         setListValues(subsList, term.subs());
         setListValues(freeVarsList, term.freeVars());
         setListValues(boundVarsList, term.boundVars());
         SWTUtil.setText(javaBlockText, ObjectUtil.toString(term.javaBlock()));
         setListValues(labelList, term.getLabels());
         SWTUtil.setText(hashCodeText, term.hashCode() + StringUtil.EMPTY_STRING);
      }
      else {
         sortText.setText(StringUtil.EMPTY_STRING);
         opText.setText(StringUtil.EMPTY_STRING);
         subsList.removeAll();
         freeVarsList.removeAll();
         boundVarsList.removeAll();
         javaBlockText.setText(StringUtil.EMPTY_STRING);
         labelList.removeAll();
         hashCodeText.setText(StringUtil.EMPTY_STRING);
      }
   }
   
   public static String operatorToString(Operator op) {
      if (op != null) {
         return op.getClass().getSimpleName() + " (Name = " + op.toString() + ", Arity = " + op.arity() + ", Rigid = " + op.isRigid() + ")";
      }
      else {
         return null;
      }
   }
   
   /**
    * Converts the given {@link PosInSequent} into a human readable {@link String}.
    * @param pis The {@link PosInSequent} to convert.
    * @return The human readable {@link String}.
    */
   public static String posInSequentToString(PosInSequent pis) {
      StringBuffer sb = new StringBuffer();
      if (pis != null) {
         if (pis.isSequent()) {
            sb.append("Sequent");
         }
         else {
            PosInOccurrence pio = pis.getPosInOccurrence();
            if (pio != null) {
               if (pio.isInAntec()) {
                  sb.append("Antecedent at ");
               }
               else {
                  sb.append("Succedent at ");
               }
               if (pio.posInTerm() != null) {
                  if (pio.isTopLevel()) {
                     sb.append("Top Level");
                  }
                  else {
                     PosInTerm pit = pio.posInTerm();
                     if (pit != null) {
                        sb.append(pit.integerList(pit.iterator()));
                        ;
                     }
                  }
                  sb.append(" of " + pio.constrainedFormula());
               }
            }
         }
      }
      return sb.toString();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (editor != null) {
         editor.removePropertyChangeListener(listener);
      }
      super.dispose();
   }
}
