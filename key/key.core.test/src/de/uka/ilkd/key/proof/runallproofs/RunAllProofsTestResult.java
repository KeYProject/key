package de.uka.ilkd.key.proof.runallproofs;

import java.io.Serializable;

public class RunAllProofsTestResult implements Serializable {
   public final String message;
   public final boolean success;

   public RunAllProofsTestResult(String message, boolean success) {
      this.message = message;
      this.success = success;
   }
}