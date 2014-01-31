package de.uka.ilkd.key.proof.io.event;

import java.util.EventObject;

import de.uka.ilkd.key.proof.io.ProofSaver;

/**
 * An event thrown by a {@link ProofSaver}.
 * @author Martin Hentschel
 */
public class ProofSaverEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = 6000441441638546982L;

   /**
    * The file name.
    */
   private final String filename;
   
   /**
    * The error message.
    */
   private final String errorMsg;
   
   /**
    * Constructor.
    * @param source The {@link ProofSaver} which throws this event.
    * @param filename The file name.
    * @param errorMsg The error message.
    */
   public ProofSaverEvent(ProofSaver source, String filename, String errorMsg) {
      super(source);
      this.filename = filename;
      this.errorMsg = errorMsg;
   }

   /**
    * Returns the file name.
    * @return The file name.
    */
   public String getFilename() {
      return filename;
   }

   /**
    * Returns the error message.
    * @return The error message.
    */
   public String getErrorMsg() {
      return errorMsg;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ProofSaver getSource() {
      return (ProofSaver)super.getSource();
   }
}
