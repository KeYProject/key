package de.uka.ilkd.key.proof.runallproofs;

import java.io.Serializable;

public class SuccessReport implements Serializable {
   final String message;
   final boolean success;

   SuccessReport(String message, boolean success) {
      this.message = message;
      this.success = success;
   }
}