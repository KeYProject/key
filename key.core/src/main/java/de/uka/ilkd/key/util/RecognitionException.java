/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.net.MalformedURLException;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.parsing.HasLocation;

import org.antlr.v4.runtime.IntStream;

/**
 * @author Alexander Weigl
 * @version 1 (09.02.23)
 */
public class RecognitionException extends Exception implements HasLocation {
    public IntStream input;
    public Position position;
    public int charPositionInLine;

    public RecognitionException(IntStream input, Position position) {
        this.input = input;
        this.position = position;
    }

    public Position getPosition() {
        return position;
    }

    @Nullable
    @Override
    public Location getLocation() throws MalformedURLException {
        return new Location(MiscTools.getURIFromTokenSource(input.getSourceName()), position);
    }
}
