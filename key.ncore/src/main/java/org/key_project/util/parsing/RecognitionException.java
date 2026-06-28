/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.parsing;



import org.antlr.v4.runtime.IntStream;

/**
 * @author Alexander Weigl
 * @version 1 (09.02.23)
 */
public class RecognitionException extends Exception implements HasLocation {
    public IntStream input;
    public Position position;

    public RecognitionException(IntStream input, Position position) {
        this.input = input;
        this.position = position;
    }

    public Position getPosition() {
        return position;
    }

    @Override
    public Location getLocation() {
        return new Location(SourceNames.getURIFromTokenSource(input.getSourceName()), position);
    }
}
