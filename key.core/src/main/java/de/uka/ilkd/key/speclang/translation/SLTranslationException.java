/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.translation;

import java.net.MalformedURLException;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.util.parsing.HasLocation;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public class SLTranslationException extends ProofInputException implements HasLocation {
    protected final @NonNull Location location;

    public SLTranslationException(@NonNull String message, @NonNull Throwable cause,
            @NonNull Location location) {
        super(message, cause);
        if (location == null) {
            throw new IllegalArgumentException();
        }
        this.location = location;
    }

    public SLTranslationException(@NonNull String message, @NonNull Location location,
            @NonNull Throwable cause) {
        this(message, cause, location);
    }

    public SLTranslationException(@NonNull String message, @NonNull Location location) {
        this(message, null, location);
    }

    public SLTranslationException(@NonNull String message) {
        this(message, null, new Location(null, Position.UNDEFINED));
    }

    @Override
    public @Nullable Location getLocation() throws MalformedURLException {
        return location;
    }
}
