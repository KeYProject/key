package de.hentschel.visualdbc.statistic.ui.adapter;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.gef.EditPart;
import org.eclipse.gmf.runtime.notation.View;
import org.eclipse.ui.IEditorPart;

import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditor;
import de.hentschel.visualdbc.statistic.ui.control.IProofReferenceProvider;
import de.hentschel.visualdbc.statistic.ui.view.DbcProofReferencesViewPart;
import de.hentschel.visualdbc.statistic.ui.view.IProofReferencesViewPart;

/**
 * Converts a given {@link DbCDiagramEditor} into an {@link IProofReferencesViewPart}.
 * @author Martin Hentschel
 */
public class DbCDiagramEditorProofReferenceAdapterFactory extends AbstractProofReferenceAdapterFactory {
   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Object getAdapter(Object adaptableObject, Class adapterType) {
      if (adaptableObject instanceof IEditorPart) {
         IProofReferenceProvider provider = new IProofReferenceProvider() {
            @Override
            public List<?> extractElementsToShow(List<?> elements) {
               List<Object> result = new LinkedList<Object>();
               if (elements != null) {
                  for (Object element : elements) {
                     if (element instanceof EditPart) {
                        element = ((EditPart)element).getModel();
                     }
                     if (element instanceof View) {
                        element = ((View)element).getElement();
                     }
                     result.add(element);
                  }
               }
               return result;
            }
         };
         return new DbcProofReferencesViewPart((IEditorPart)adaptableObject, provider);
      }
      else {
         return null;
      }
   }
}
