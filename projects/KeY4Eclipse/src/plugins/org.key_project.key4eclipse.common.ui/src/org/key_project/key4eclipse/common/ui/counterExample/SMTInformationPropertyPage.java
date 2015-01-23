package org.key_project.key4eclipse.common.ui.counterExample;

import java.util.List;

import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.jface.viewers.ColumnViewerToolTipSupport;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.dialogs.PropertyPage;
import org.eclipse.ui.internal.WorkbenchPlugin;
import org.eclipse.ui.internal.ide.IDEInternalWorkbenchImages;
import org.key_project.key4eclipse.common.ui.counterExample.EclipseCounterExampleGenerator.InformationMessage;
import org.key_project.key4eclipse.common.ui.counterExample.EclipseCounterExampleGenerator.SMTProblemPreferenceNode;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.gui.smt.SolverListener.InternSMTProblem;

/**
 * A {@link PropertyPage} which shows the information collect during counter example generation.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class SMTInformationPropertyPage extends PropertyPage {
   /**
    * The {@link SMTProblemPreferenceNode} in which this {@link PropertyPage} is shown.
    */
   private final SMTPreferenceDialog dialog;
   
   /**
    * The {@link InformationMessage}s to show.
    */
   private final List<InformationMessage> information;

   /**
    * Constructor.
    * @param dialog The {@link SMTProblemPreferenceNode} in which this {@link PropertyPage} is shown.
    * @param information The {@link InformationMessage}s to show.
    */
   public SMTInformationPropertyPage(SMTPreferenceDialog dialog, List<InformationMessage> information) {
      this.dialog = dialog;
      this.information = information;
      noDefaultAndApplyButton();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Control createContents(Composite parent) {
      TableViewer informationViewer = new TableViewer(parent);
      informationViewer.setContentProvider(ArrayContentProvider.getInstance());
      informationViewer.setInput(information);
      informationViewer.setLabelProvider(new ColumnLabelProvider() {
         @Override
         public String getText(Object element) {
            if (element instanceof InformationMessage) {
               return ((InformationMessage) element).getTitle();
            }
            else {
               return super.getText(element);
            }
         }
         
         @Override
         public Image getImage(Object element) {
            if (element instanceof InformationMessage) {
               if (((InformationMessage) element).isError()) {
                  return WorkbenchPlugin.getDefault().getSharedImages().getImage(IDEInternalWorkbenchImages.IMG_OBJS_ERROR_PATH);
               }
               else {
                  return WorkbenchPlugin.getDefault().getSharedImages().getImage(IDEInternalWorkbenchImages.IMG_OBJS_WARNING_PATH);
               }
            }
            else {
               return super.getImage(element);
            }
         }

         @Override
         public String getToolTipText(Object element) {
            if (element instanceof InformationMessage) {
               InformationMessage message = (InformationMessage) element;
               if (message.getData() instanceof String) {
                  return (String) message.getData();
               }
               else {
                  return super.getToolTipText(element);
               }
            }
            else {
               return super.getToolTipText(element);
            }
         }
      });
      ColumnViewerToolTipSupport.enableFor(informationViewer);
      informationViewer.addDoubleClickListener(new IDoubleClickListener() {
         @Override
         public void doubleClick(DoubleClickEvent event) {
            handleDoubleClick(event);
         }
      });
      return informationViewer.getControl();
   }

   /**
    * Handles a double click.
    * @param event The event.
    */
   protected void handleDoubleClick(DoubleClickEvent event) {
      Object[] elements = SWTUtil.toArray(event.getSelection());
      for (Object element : elements) {
         if (element instanceof InformationMessage) {
            InformationMessage message = (InformationMessage) element;
            if (message.getData() instanceof InternSMTProblem) {
               dialog.setCurrentPageId(EclipseCounterExampleGenerator.computeProblemId((InternSMTProblem) message.getData()));
            }
         }
      }
   }
}
