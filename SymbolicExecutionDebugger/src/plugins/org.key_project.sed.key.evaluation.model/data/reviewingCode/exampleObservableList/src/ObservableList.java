import java.util.LinkedList;
import java.util.List;

/**
 * An observable list which delegates all actions to a base {@link List}.
 * <p>
 * For simplicity, only adding elements via {@link #add(Object)} is supported.
 * @see ListListener
 * @see ListEvent
 */
public class ObservableList {
   /**
    * The base {@link List} to which all actions are delegated.
    * <p>
    * The base {@link List} is never {@code null}.
    */
   private final /*@ non_null @*/ List list;
   
   /**
    * The optional available {@link ListListener}.
    * <p>
    * If no listeners are available the array might be {@code null} or empty.
    */
   private /*@ nullable @*/ ListListener[] listListeners;
   
   /**
    * Constructor.
    * @param list The optional base {@link List} to which all actions are delegated.
    */
   public ObservableList(List list) {
      if (list != null) {
         this.list = list;
      }
      else {
         this.list = new LinkedList();
      }
   }

   /**
    * Adds the given element add the end to the list by calling
    * {@link List#add(Object)}.
    * @param element The element to add.
    * @return {@code true} if list has been changed, {@code false} otherwise.
    */
   public boolean add(Object element) {
      boolean result = list.add(element);
      if (result) {
         fireElementAdded(new ListEvent(this, element));
      }
      return result;
   }
   
   /**
    * Returns the available {@link ListListener}.
    * @return The available {@link ListListener}.
    */
   public ListListener[] getListListeners() {
      return listListeners;
   }

   /**
    * Sets the available {@link ListListener}.
    * @param listListeners The new {@link ListListener}.
    */
   public void setListListeners(ListListener[] listListeners) {
      this.listListeners = listListeners;
   }

   /**
    * Informs all available {@link ListListener} about an added element
    * by calling {@link ListListener#elementAdded(ListEvent)}.
    * @param e The {@link ListEvent} containing all event details.
    */
   protected void fireElementAdded(ListEvent e) {
      if (listListeners != null) {
         /*@ loop_invariant i >= 0 && i <= listListeners.length;
           @ decreasing listListeners.length - i;
           @ assignable \everything;
           @*/
         for (int i = 0; i < listListeners.length; i++) {
            if (listListeners[i] != null) {
               listListeners[i].elementAdded(e);
            }
         }
      }
   }
}
