package org.key_project.util.eclipse.swt.viewer.event;

import java.util.EventObject;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Item;

/**
 * An event thrown from a {@link Viewer} when an {@link Item} was updated.
 * @author Martin Hentschel
 */
public class ViewerUpdateEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = -6164334425179326188L;

   /**
    * The updated item.
    */
   private final Item item;
   
   /**
    * The new {@link Object} represented by the {@link Item}.
    */
   private final Object element;
   
   /**
    * Constructor
    * @param source The {@link Viewer} which has thrown the event.
    * @param item The updated item.
    * @param element The new {@link Object} represented by the {@link Item}.
    */
   public ViewerUpdateEvent(Viewer source, Item item, Object element) {
      super(source);
      this.item = item;
      this.element = element;
   }

   /**
    * Returns the updated item.
    * @return The updated item.
    */
   public Item getItem() {
      return item;
   }

   /**
    * Returns the new {@link Object} represented by the {@link Item}.
    * @return The new {@link Object} represented by the {@link Item}.
    */
   public Object getElement() {
      return element;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Viewer getSource() {
      return (Viewer)super.getSource();
   }
}
