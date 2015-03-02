package org.key_project.sed.ui.edit;

import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.annotation.impl.SearchAnnotation;
import org.key_project.sed.ui.wizard.SearchWizard;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;

/**
 * An {@link ISEDAnnotationEditor} to edit {@link SearchAnnotation}s.
 * @author Martin Hentschel
 */
public class SearchAnnotationEditor extends AbstractSEDAnnotationEditor {
   /**
    * Defines the search text.
    */
   private Text searchText;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Control createContent(Composite parent) {
      Group searchGroup = new Group(parent, SWT.NONE);
      searchGroup.setText("Search");
      searchGroup.setLayout(new GridLayout(2, false));
      Label searchLabel = new Label(searchGroup, SWT.NONE);
      searchLabel.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, false, false));
      searchLabel.setText("&Text");
      searchText = new Text(searchGroup, SWT.BORDER | SWT.MULTI);
      searchText.setLayoutData(new GridData(GridData.FILL_BOTH));
      Assert.isTrue(getAnnotation() instanceof SearchAnnotation);
      searchText.setText(((SearchAnnotation)getAnnotation()).getSearch());
      searchText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            updateErrorMessage();
         }
      });
      return searchGroup;
   }

   /**
    * Updates the shown error message.
    */
   protected void updateErrorMessage() {
      boolean valid = !StringUtil.isTrimmedEmpty(searchText.getText());
      setErrorMessage(valid ? null : "No text defined.");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void applyChanges(IProgressMonitor monitor) throws Exception {
      // Perform search
      monitor.beginTask("Performing search", IProgressMonitor.UNKNOWN);
      Assert.isTrue(getAnnotation() instanceof SearchAnnotation);
      IRunnableWithResult<String> searchRun = new AbstractRunnableWithResult<String>() {
         @Override
         public void run() {
            setResult(searchText.getText());
         }
      };
      searchText.getDisplay().syncExec(searchRun);
      SearchAnnotation annotation = (SearchAnnotation)getAnnotation();
      if (!searchRun.getResult().equals(annotation.getSearch())) {
         List<ISEDAnnotationLink> links = SearchWizard.search(annotation.getType(), annotation, getTarget(), searchRun.getResult(), monitor);
         // Edit annotation
         SWTUtil.checkCanceled(monitor);
         annotation.setSearch(searchRun.getResult());
         monitor.worked(1);
         ISEDAnnotationLink[] oldLinks = annotation.getLinks();
         for (ISEDAnnotationLink link : oldLinks) {
            link.getTarget().removeAnnotationLink(link);
            monitor.worked(1);
         }
         monitor.worked(1);
         for (ISEDAnnotationLink link : links) {
            link.getTarget().addAnnotationLink(link);
            monitor.worked(1);
         }
      }
      monitor.done();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean needsProgressMonitor() {
      return true;
   }
}
