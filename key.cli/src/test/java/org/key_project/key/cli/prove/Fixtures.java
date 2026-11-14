/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Path;

/**
 * Resolves the test fixtures on the test runtime classpath.
 */
final class Fixtures {
    private Fixtures() {
    }

    /// The load file of the two-method fixture {@code C} (one closed, one open contract).
    static Path indexKey() {
        return resource("/fixtures/index/index.key");
    }

    static Path resource(String name) {
        URL url = Fixtures.class.getResource(name);
        if (url == null) {
            throw new IllegalStateException("test resource not found: " + name);
        }
        try {
            return Path.of(url.toURI());
        } catch (URISyntaxException e) {
            throw new IllegalStateException("invalid test resource URI: " + url, e);
        }
    }
}
