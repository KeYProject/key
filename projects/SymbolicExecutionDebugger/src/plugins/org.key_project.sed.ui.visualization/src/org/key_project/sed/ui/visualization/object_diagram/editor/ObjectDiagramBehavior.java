package org.key_project.sed.ui.visualization.object_diagram.editor;

import org.eclipse.graphiti.ui.editor.DiagramBehavior;
import org.eclipse.graphiti.ui.editor.IDiagramContainerUI;
import org.key_project.sed.ui.visualization.util.EmptyDiagramPersistencyBehavior;

public class ObjectDiagramBehavior extends DiagramBehavior {
   /**
    * Indicates that this editor is read-only or editable otherwise.
    */
   private boolean readOnly;

   public ObjectDiagramBehavior(IDiagramContainerUI diagramContainer, boolean readOnly) {
      super(diagramContainer);
      this.readOnly = readOnly;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected EmptyDiagramPersistencyBehavior createPersistencyBehavior() {
      return new EmptyDiagramPersistencyBehavior(this);
   }
   
   /**
    * Checks if this editor is read-only or editable.
    * @return {@code true} read-only, {@code false} editable
    */
   public boolean isReadOnly() {
      return readOnly;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isDirty() {
      return !isReadOnly() && super.isDirty();
   }
}
