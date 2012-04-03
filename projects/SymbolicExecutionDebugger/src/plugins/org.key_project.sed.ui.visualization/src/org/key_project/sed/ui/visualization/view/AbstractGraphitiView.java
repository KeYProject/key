package org.key_project.sed.ui.visualization.view;

import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.gef.ui.palette.FlyoutPaletteComposite.FlyoutPreferences;
import org.eclipse.graphiti.ui.editor.DiagramEditor;
import org.eclipse.graphiti.ui.editor.DiagramEditorActionBarContributor;
import org.eclipse.ui.IEditorActionBarContributor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;
import org.key_project.util.eclipse.view.editorInView.AbstractEditorInViewView;

public abstract class AbstractGraphitiView extends AbstractEditorInViewView {
   @Override
   protected IEditorPart createEditorPart() {
      return new DiagramEditor() {
         @SuppressWarnings("restriction")
         @Override
         protected FlyoutPreferences getPalettePreferences() {
            // Disable the palette: see http://www.eclipse.org/forums/index.php/t/263112/
            final FlyoutPreferences superPreferences = super.getPalettePreferences(); // Modification of this preferences is not possible, because the changes are shared with real editors
            return new FlyoutPreferences() {
               @Override
               public int getDockLocation() {
                  return superPreferences.getDockLocation();
               }

               @Override
               public int getPaletteState() {
                  return 8; // org.eclipse.gef.ui.palette.FlyoutPaletteComposite.STATE_HIDDEN
               }

               @Override
               public int getPaletteWidth() {
                  return superPreferences.getPaletteWidth();
               }

               @Override
               public void setDockLocation(int location) {
                  superPreferences.setDockLocation(location);
               }

               @Override
               public void setPaletteState(int state) {
                  superPreferences.setPaletteState(state);
               }

               @Override
               public void setPaletteWidth(int width) {
                  superPreferences.setPaletteWidth(width);
               }
            };
         }
      };
   }
   
   @Override
   protected IEditorActionBarContributor createEditorActionBarContributor() {
      return new DiagramEditorActionBarContributor();
   }

   @Override
   protected IEditorInput getEditorInput() {
      return new FileEditorInput(ResourcesPlugin.getWorkspace().getRoot().getProject("General").getFile(new Path("src/diagrams/newDiagram.diagram")));
   }
}
