/**
 * 
 */
package de.uka.ilkd.key.proof;

/**
 * Default implementation of a {@link TaskStartedInfo}. 
 */
public class DefaultTaskStartedInfo implements TaskStartedInfo {
   
   private final TaskStartedInfo.TaskKind kind;
   private final String message;
   private final int size;
   
   public DefaultTaskStartedInfo(TaskKind kind, String message, int size) {
      super();
      this.kind = kind;
      this.message = message;
      this.size = size;
   }

   @Override
   public String toString() {
      return "DefaultTaskStartedInfo [kind=" + kind + ", message=" + message
            + ", size=" + size + "]";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public TaskKind getKind() {
      return kind;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getMessage() {
      return message;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getSize() {
      return size;
   }

}
