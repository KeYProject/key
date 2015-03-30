package org.key_project.util.eclipse.preference.event;

import java.util.EventObject;

import org.eclipse.jface.preference.FieldEditor;

/**
 * An event thrown by a {@link FieldEditor}.
 * @author Martin Hentschel
 */
public class FieldEditorValueEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = 4619378618129448291L;

   /**
    * Constructor.
    * @param source The {@link FieldEditor} which has thrown this event.
    */
   public FieldEditorValueEvent(FieldEditor source) {
      super(source);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public FieldEditor getSource() {
      return (FieldEditor)super.getSource();
   }
}
