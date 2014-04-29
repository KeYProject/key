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

package de.hentschel.visualdbc.generation.ui.wizard;

import java.lang.reflect.InvocationTargetException;
import java.util.Map;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.emf.common.util.URI;
import org.eclipse.jface.operation.IRunnableWithProgress;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSDriver;
import de.hentschel.visualdbc.datasource.ui.wizard.page.DataSourceWizardPage;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCCreationWizard;
import de.hentschel.visualdbc.generation.operation.CreateOperation;
import de.hentschel.visualdbc.generation.ui.util.LogUtil;

/**
 * A wizard to create a new diagram that is filled with the content from
 * a data source.
 * @author Martin Hentschel
 */
public class GenerateDiagramWizard extends DbCCreationWizard {
   /**
    * The wizard page with the data source settings.
    */
   private DataSourceWizardPage dataSourcePage;

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      super.addPages();
      dataSourcePage = new DataSourceWizardPage("dataSourcePage", getSelection());
      addPage(dataSourcePage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      try {
         final IDSDriver driver = dataSourcePage.getDriver();
         final Map<String, Object> settings = dataSourcePage.getValues();
         final URI modelURI = domainModelFilePage.getURI();
         final URI diagramURI = diagramModelFilePage.getURI();
         IRunnableWithProgress runnable = new IRunnableWithProgress() {
            @Override
            public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
               try {
                  IDSConnection connection = driver.createConnection();
                  connection.connect(settings, false, monitor);
                  CreateOperation co = new CreateOperation(connection, modelURI, diagramURI);
                  co.execute(monitor, true);
               }
               catch (OperationCanceledException e) {
                  throw new InterruptedException();
               }
               catch (Exception e) {
                  throw new InvocationTargetException(e);
               }
            }
         };
         getContainer().run(true, false, runnable);
         return true;
      }
      catch (InvocationTargetException e) {
         LogUtil.getLogger().logError(e); 
         LogUtil.getLogger().openErrorDialog(getShell(), e.getTargetException());
         return false;
      }
      catch (InterruptedException e) {
         return false; // Canceled
      }
   }
}