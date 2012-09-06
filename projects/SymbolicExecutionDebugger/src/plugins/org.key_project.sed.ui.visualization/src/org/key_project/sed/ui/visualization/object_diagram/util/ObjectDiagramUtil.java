package org.key_project.sed.ui.visualization.object_diagram.util;

import java.util.List;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.mm.pictograms.Anchor;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.key_project.sed.ui.visualization.model.od.ODFactory;
import org.key_project.sed.ui.visualization.model.od.ODModel;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;

/**
 * Provides static methods for object diagrams.
 * @author Martin Hentschel
 */
public final class ObjectDiagramUtil {
   /**
    * File extension for diagram file with included model.
    */
   public static final String DIAGRAM_AND_MODEL_FILE_EXTENSION = "od";

   /**
    * File extension for diagram file with included model with leading {@code '.'} character.
    */
   public static final String DIAGRAM_AND_MODEL_FILE_EXTENSION_WITH_DOT = "." + DIAGRAM_AND_MODEL_FILE_EXTENSION;

   /**
    * Forbid instances.
    */
   private ObjectDiagramUtil() {
   }
   
   /**
    * Returns the {@link ODModel} which contains all business objects of
    * the given object diagram. If no one is available a new {@link ODModel} 
    * instance is created and add to the resource of the diagram.
    * @param diagram The {@link Diagram}.
    * @return The found or created {@link ODModel}.
    */
   public static ODModel getModel(Diagram diagram) {
      if (diagram != null && diagram.eResource() != null) {
         List<EObject> content = diagram.eResource().getContents();
         EObject modelCandidate = CollectionUtil.search(content, new IFilter<EObject>() {
            @Override
            public boolean select(EObject element) {
               return element instanceof ODModel;
            }
         });
         if (modelCandidate instanceof ODModel) {
            return (ODModel)modelCandidate;
         }
         else {
            ODModel newModel = ODFactory.eINSTANCE.createODModel();
            diagram.eResource().getContents().add(newModel);
            return newModel;
         }
      }
      else {
         return ODFactory.eINSTANCE.createODModel();
      }
   }

   /**
    * Returns the {@link ODObject} belonging to the anchor, or {@code null} if not available.
    * @param fp The {@link IFeatureProvider} to use.
    * @param anchor The {@link Anchor} to get its business object.
    * @return The found business object or {@code null} if not available.
    */
   public static ODObject getObject(IFeatureProvider fp, Anchor anchor) {
      ODObject result = null;
      if (fp != null && anchor != null) {
         Object bo = fp.getBusinessObjectForPictogramElement(anchor.getParent());
         if (bo instanceof ODObject) {
            return (ODObject)bo;
         }
      }
      return result;
   }
}
