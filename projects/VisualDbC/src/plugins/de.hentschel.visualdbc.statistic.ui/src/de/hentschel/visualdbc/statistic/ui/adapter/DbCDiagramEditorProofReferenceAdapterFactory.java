package de.hentschel.visualdbc.statistic.ui.adapter;

import java.util.List;

import org.eclipse.ui.IEditorPart;

import de.hentschel.visualdbc.dbcmodel.diagram.custom.util.GMFUtil;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditor;
import de.hentschel.visualdbc.statistic.ui.control.IProofReferenceProvider;
import de.hentschel.visualdbc.statistic.ui.util.StatisticUtil;
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
         final DbCDiagramEditor editor = adaptableObject instanceof DbCDiagramEditor ? (DbCDiagramEditor)adaptableObject : null;
         IProofReferenceProvider provider = new IProofReferenceProvider() {
            @Override
            public List<?> extractElementsToShow(List<?> elements) {
               return GMFUtil.getModelObjects(elements);
            }

            @Override
            public void select(List<?> toSelect) {
               StatisticUtil.select(editor, toSelect);
            }
         };
         return new DbcProofReferencesViewPart((IEditorPart)adaptableObject, provider);
      }
      else {
         return null;
      }
   }
}
