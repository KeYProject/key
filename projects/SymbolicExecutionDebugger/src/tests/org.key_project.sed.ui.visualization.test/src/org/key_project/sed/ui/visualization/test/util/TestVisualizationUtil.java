package org.key_project.sed.ui.visualization.test.util;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.charset.Charset;
import java.util.Collections;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.transaction.RecordingCommand;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.ui.services.GraphitiUi;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.serialization.SEDXMLWriter;
import org.key_project.sed.ui.visualization.execution_tree.provider.ExecutionTreeDiagramTypeProvider;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;

/**
 * Provides static methods that make testing easier.
 * @author Martin Hentschel
 */
public final class TestVisualizationUtil {
   /**
    * Forbid instances.
    */
   private TestVisualizationUtil() {
   }
   
   /**
    * Creates an empty execution tree diagram.
    * @param diagramFile The diagram file.
    * @param modelFile The model file.
    * @return The created {@link Diagram}.
    * @throws CoreException Occurred Exception.
    * @throws IOException Occurred Exception.
    */
   public static Diagram createEmptyExecutionTreeDiagram(IFile diagramFile, IFile modelFile) throws CoreException, IOException {
      TestCase.assertNotNull(diagramFile);
      TestCase.assertNotNull(modelFile);
      // Create model file
      SEDXMLWriter writer = new SEDXMLWriter();
      String modelContent = writer.toXML(new ISEDDebugTarget[0], "UTF-8");
      if (!modelFile.exists()) {
         modelFile.create(new ByteArrayInputStream(modelContent.getBytes(Charset.forName("UTF-8"))), true, null);
      }
      else {
         modelFile.setContents(new ByteArrayInputStream(modelContent.getBytes(Charset.forName("UTF-8"))), true, true, null);
      }
      // Create diagram file
      final Diagram diagram = Graphiti.getPeCreateService().createDiagram(ExecutionTreeDiagramTypeProvider.TYPE, "Test", true);
      URI diagramURI = URI.createPlatformResourceURI(diagramFile.getFullPath().toString(), true);
      TransactionalEditingDomain domain = GraphitiUtil.createDomainAndResource(diagram, diagramURI); 
      final URI domainURI = URI.createPlatformResourceURI(modelFile.getFullPath().toString(), true);
      domain.getCommandStack().execute(new RecordingCommand(domain, "Set link to model file.") {
         @Override
         protected void doExecute() {
            GraphitiUi.getPeService().setPropertyValue(diagram, ExecutionTreeUtil.USER_PROPERTY_DOMAIN_MODEL_FILE, domainURI.toString());
         }

         @Override
         public boolean canUndo() {
            return false;
         }
      });
      diagram.eResource().save(Collections.EMPTY_MAP);
      return diagram;
   }
}
