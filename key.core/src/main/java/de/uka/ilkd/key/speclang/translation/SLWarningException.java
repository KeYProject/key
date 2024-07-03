/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.speclang.PositionedString;


public class SLWarningException extends SLTranslationException {

    /**
     *
     */
    private static final long serialVersionUID = 699191378589840435L;


    public SLWarningException(String text, String fileName, Position pos) {
        super(text, fileName, pos);
    }


    public SLWarningException(PositionedString warning) {
        this(warning.text, warning.fileName, warning.pos);
    }


    public PositionedString getWarning() {
        return new PositionedString(getMessage(), getFileName(), getPosition());
    }
}
