package de.uka.ilkd.key.proof;

/** 
 * Used as an event object to inform about a prover task
 * that is just about to start. 
 */
public interface TaskStartedInfo {

   public enum TaskKind {
      Strategy, Macro, UserInterface, Loading, Other;
   }
   
   /**
    * allows to query about the nature of task
    * @return the kind of the task
    */
   public TaskKind getKind();
   
   /**
    * returns a message with a description of the task, example: "Processing Strategy"
    */
   public String getMessage();
   
   /**
   * returns measure for the total size of the task. The number indicates the amount of work needed to complete the task,
   * mostly used by the GUI to display a progress bar. A returned value of 0 means unknown size.
   */
   public int getSize();
   
}
