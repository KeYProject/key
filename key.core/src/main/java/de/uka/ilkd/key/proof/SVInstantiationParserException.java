/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.java.Position;
import org.jspecify.annotations.Nullable;

import java.util.Optional;

public class SVInstantiationParserException extends SVInstantiationExceptionWithPosition {
    private final String instantiation;
    private final String detail;

    public SVInstantiationParserException(String instantiation, Position position,
                                          @Nullable String detail,
                                          boolean inIfSequent) {
        super("Parser Error", position, inIfSequent);
        this.instantiation = instantiation;
        this.detail = (detail == null) ? "" : detail;
    }

    private Optional<String> getInstantiationRow() {
        if (getPosition().column() <= 0) {
            return Optional.empty();
        }
        String[] rows = instantiation.split("\n");
        var line = getPosition().line() - 1;
        if (!(line < rows.length)) {
            return Optional.empty();
        }
        return Optional.of(rows[line]);
    }

    public String getMessage() {
        int column = getPosition().column();

        String msg = super.getMessage();
        // needs non-prop font: msg +="\n"+inst;
        Optional<String> row = getInstantiationRow();
        if (row.isPresent()) {
            // needs non-prop font: msg +="\n"+space(column-1)+"^";
            var sb = new StringBuilder(row.get());
            sb.insert(column - 1, " ~~> ");
            msg += "\noccurred at: " + sb;
        } else {
            msg += "\noccurred in: " + instantiation;
        }

        msg += "\nDetail:\n" + detail;

        return msg;
    }

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
        return getMessage();
    }

    @Override
    public SVInstantiationParserException initCause(@Nullable Throwable cause) {
        super.initCause(cause);
        return this;
    }
}
