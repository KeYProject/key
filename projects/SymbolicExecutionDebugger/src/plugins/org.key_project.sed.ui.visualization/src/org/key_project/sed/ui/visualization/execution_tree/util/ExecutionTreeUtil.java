package org.key_project.sed.ui.visualization.execution_tree.util;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.URIConverter;
import org.eclipse.emf.ecore.resource.impl.ExtensibleURIConverterImpl;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.ui.services.GraphitiUi;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

/**
 * Provides static utility methods for execution tree diagrams.
 * @author Martin Hentschel
 */
public final class ExecutionTreeUtil {
   /**
    * The file extension of Symbolic Execution Tree diagram files.
    */
   public static final String DIAGRAM_FILE_EXTENSION = "set_diagram";

   /**
    * The file extension of Symbolic Execution Tree diagram files with leading dot.
    */
   public static final String DIAGRAM_FILE_EXTENSION_WITH_DOT = "." + DIAGRAM_FILE_EXTENSION;
   
   /**
    * The file extension of Symbolic Execution Tree domain model files.
    */
   public static final String DOMAIN_FILE_EXTENSION = "set";

   /**
    * The file extension of Symbolic Execution Tree domain model files with leading dot.
    */
   public static final String DOMAIN_FILE_EXTENSION_WITH_DOT = "." + DOMAIN_FILE_EXTENSION;
   
   /**
    * User defined property for {@link Diagram} instances which contains
    * a URI to the domain model file as value. The value can be read/set via
    * {@link GraphitiUi#getPeService()}.
    */
   public static final String USER_PROPERTY_DOMAIN_MODEL_FILE = "domainModelFile";
   
   /**
    * Forbid instances.
    */
   private ExecutionTreeUtil() {
   }
   
   /**
    * Returns the {@link URI} to the domain file of the given {@link Diagram}. 
    * @param diagram The given {@link Diagram}.
    * @return The {@link URI} to the domain file.
    * @throws IOException Occurred Exception.
    */
   public static URI getDomainFileURI(Diagram diagram) throws IOException {
      if (diagram != null) {
         String uriString = GraphitiUi.getPeService().getPropertyValue(diagram, USER_PROPERTY_DOMAIN_MODEL_FILE);
         if (!StringUtil.isEmpty(uriString)) {
            return URI.createURI(uriString);
         }
         else {
            throw new IOException("Diagram provides no domain model file.");
         }
      }
      else {
         throw new IOException("No Diagram defined.");
      }
   }
   
   /**
    * Opens an {@link InputStream} to the domain file of the given {@link Diagram}.
    * @param diagram The {@link Diagram} which provides the domain file.
    * @return The opened {@link InputStream}.
    * @throws IOException Occurred Exception.
    */
   public static InputStream readDomainFile(Diagram diagram) throws IOException {
      URI uri = getDomainFileURI(diagram);
      URIConverter converter = new ExtensibleURIConverterImpl();
      return converter.createInputStream(uri);
   }
   
   /**
    * Opens an {@link OutputStream} to the domain file of the given {@link Diagram}.
    * @param diagram The {@link Diagram} which provides the domain file.
    * @return The opened {@link OutputStream}.
    * @throws IOException Occurred Exception.
    */
   public static OutputStream writeDomainFile(Diagram diagram) throws IOException {
      URI uri = getDomainFileURI(diagram);
      URIConverter converter = new ExtensibleURIConverterImpl();
      return converter.createOutputStream(uri);
   }
   
   /**
    * Computes for the given diagram file the corresponding model file.
    * @param diagramFile The given diagram file.
    * @return The corresponding model file or {@code null} if the model file is given or it is not possible to compute it.
    */
   public static String getInitialDomainFileName(String diagramFile) {
      String name = IOUtil.getFileNameWithoutExtension(diagramFile);
      if (name != null) {
         return name + DOMAIN_FILE_EXTENSION_WITH_DOT;
      }
      else {
         return null;
      }
   }
}
