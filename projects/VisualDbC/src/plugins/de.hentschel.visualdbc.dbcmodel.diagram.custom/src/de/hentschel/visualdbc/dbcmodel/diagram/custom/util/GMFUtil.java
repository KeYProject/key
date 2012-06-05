package de.hentschel.visualdbc.dbcmodel.diagram.custom.util;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPartViewer;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ConnectionEditPart;
import org.key_project.util.java.ObjectUtil;

/**
 * Provides utility methods for GMF.
 * @author Martin Hentschel
 */
public final class GMFUtil {
   /**
    * Forbid instances.
    */
   private GMFUtil() {
   }

   /**
    * Returns all {@link EditPart}s although if they are not contained in the 
    * containment hierarchy, like {@link ConnectionEditPart}s.
    * @param parent The parent that has a reference to the viewer.
    * @param toSearch The {@link EObject} for that the {@link EditPart} is needed.
    * @return The found {@link EditPart}s or {@code null} if no one were found.
    */
   public static Collection<EditPart> findEditParts(EditPart parent, EObject toSearch) {
      return findEditParts(parent.getViewer(), toSearch);
   }

   /**
    * Returns all {@link EditPart}s although if they are not contained in the 
    * containment hierarchy, like {@link ConnectionEditPart}s.
    * @param viewer The viewer to use.
    * @param toSearch The {@link EObject} for that the {@link EditPart} is needed.
    * @return The found {@link EditPart}s or {@code null} if no one were found.
    */
   public static Collection<EditPart> findEditParts(EditPartViewer viewer, EObject toSearch) {
      Map<?, ?> map = viewer.getEditPartRegistry();
      Collection<?> entries = map.values();
      Iterator<?> entryIter = entries.iterator();
      Collection<EditPart> result = new HashSet<EditPart>();
      while (entryIter.hasNext()) {
         Object entry = entryIter.next();
         Assert.isTrue(entry instanceof EditPart);
         EditPart editPart = (EditPart)entry;
         if (ObjectUtil.equals(editPart.getAdapter(EObject.class), toSearch)) {
            result.add(editPart);
         }
      }
      return result;
   }
}
