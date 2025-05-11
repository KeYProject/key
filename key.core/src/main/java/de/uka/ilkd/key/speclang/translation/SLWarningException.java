/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.speclang.PositionedString;

import org.jspecify.annotations.NonNull;


public class SLWarningException extends SLTranslationException {

    /**
     *
     */
    private static final long serialVersionUID = 699191378589840435L;

    public SLWarningException(@NonNull String text, @NonNull Location location) {
        super(text, location);
    }

    public @NonNull PositionedString getWarning() {
        return new PositionedString(getMessage(), location);
    }
}
