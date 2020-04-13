package org.key_project.proofmanagement.io;

/**
 * A logger for printing messages of given severity levels.
 *
 * @author Wolfram Pfeifer
 */
public interface Logger {
    /**
     * Prints a message to the logger.
     * @param message the message to print
     */
    void print(String message);

    /**
     * Prints a message with the given severity level to the logger.
     * @param logLevel the severity of the message
     * @param message the message to print
     */
    void print(LogLevel logLevel, String message);
}
