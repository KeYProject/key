/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.parsing;

import java.net.URI;
import java.net.URISyntaxException;
import java.nio.file.Path;

import org.antlr.v4.runtime.IntStream;
import org.antlr.v4.runtime.TokenSource;
import org.jspecify.annotations.Nullable;

/**
 * Utilities for turning the source name reported by an ANTLR lexer/token into a {@link URI}.
 * <p>
 * This lives in {@code key.ncore} so that language-independent parsing infrastructure (e.g.
 * {@code Location}) can use it without depending on the {@code key.core} utility classes.
 */
public final class SourceNames {

    private SourceNames() {}

    public static @Nullable URI getURIFromTokenSource(TokenSource source) {
        return getURIFromTokenSource(source.getSourceName());
    }

    public static @Nullable URI getURIFromTokenSource(String source) {
        if (IntStream.UNKNOWN_SOURCE_NAME.equals(source)) {
            return null;
        }

        try {
            URI uri = new URI(source);
            if (uri.getScheme() != null) {
                // use this URI only if there is an explicit scheme;
                // otherwise parse it as a filename
                return uri;
            }
        } catch (URISyntaxException ignored) {
        }

        return Path.of(source).toUri();
    }
}
