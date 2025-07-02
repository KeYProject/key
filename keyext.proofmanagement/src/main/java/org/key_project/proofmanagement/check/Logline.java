package org.key_project.proofmanagement.check;

import org.key_project.proofmanagement.io.LogLevel;

/**
 * A record representing a line in the output log.
 * @param level the {@link LogLevel} of the line
 * @param message the content
 */
public record Logline(LogLevel level, String message) {
    @Override
    public String toString() {
        return level + message;
    }
}
