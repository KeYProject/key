package org.key_project.proofmanagement.check;

public class ProofManagementException extends Exception {
    public ProofManagementException(String message) {
        super(message);
    }

    public ProofManagementException(String message, Throwable cause) {
        super(message, cause);
    }
}
