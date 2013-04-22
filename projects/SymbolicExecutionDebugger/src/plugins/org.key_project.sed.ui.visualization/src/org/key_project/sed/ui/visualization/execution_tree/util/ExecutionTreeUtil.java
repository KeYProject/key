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

package org.key_project.sed.ui.visualization.execution_tree.util;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.URIConverter;
import org.eclipse.emf.ecore.resource.impl.ExtensibleURIConverterImpl;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.ui.services.GraphitiUi;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
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
   
   /**
    * Returns all {@link ISEDDebugTarget}s which are linked to the
    * {@link Diagram} managed by the given {@link IDiagramTypeProvider}.
    * @param diagramTypeProvider The {@link IDiagramTypeProvider}.
    * @return The linked {@link ISEDDebugTarget}s.
    */
   public static ISEDDebugTarget[] getAllDebugTargets(IDiagramTypeProvider diagramTypeProvider) {
      List<ISEDDebugTarget> result = new LinkedList<ISEDDebugTarget>();
      if (diagramTypeProvider != null) {
         IFeatureProvider featureProvider = diagramTypeProvider.getFeatureProvider();
         if (featureProvider != null) {
            Object[] bos = featureProvider.getAllBusinessObjectsForPictogramElement(diagramTypeProvider.getDiagram());
            for (Object bo : bos) {
               if (bo instanceof ISEDDebugTarget) {
                  result.add((ISEDDebugTarget)bo);
               }
            }
         }
      }
      return result.toArray(new ISEDDebugTarget[result.size()]);
   }
   
   /**
    * Creates a {@link TransactionalEditingDomain} and a {@link Resource}
    * for an invalid {@link URI} which contains the given {@link Diagram} as only content.
    * @param diagram The {@link Diagram} to add to a new {@link Resource}.
    * @return The used {@link TransactionalEditingDomain}.
    */
   public static TransactionalEditingDomain createDomainAndResource(Diagram diagram) {
      URI uri = URI.createURI("INVALID" + ExecutionTreeUtil.DIAGRAM_FILE_EXTENSION_WITH_DOT);
      return GraphitiUtil.createDomainAndResource(diagram, uri);
   }
}