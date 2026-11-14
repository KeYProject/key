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
public final class Fixtures {
    private Fixtures() {
    }

    /// The load file of the two-method fixture {@code C} (one closed, one open contract).
    public static Path indexKey() {
        return resource("/fixtures/index/index.key");
    }

    /// The load file selecting the closed {@code one()} contract via {@code \chooseContract}.
    public static Path chooseKey() {
        return resource("/fixtures/index/choose.key");
    }

    /// The load file selecting the closed {@code one()} contract via {@code \proofObligation}.
    public static Path proofObligationKey() {
        return resource("/fixtures/index/proofobl.key");
    }

    /// A syntactically invalid load file that cannot be loaded.
    public static Path corruptKey() {
        return resource("/fixtures/corrupt/corrupt.key");
    }

    /// The overflow-sensitive contract used to differentiate {@code intRules} settings (E3).
    public static Path overflowKey() {
        return resource("/fixtures/overflow/overflow.key");
    }

    /// The §5.2 example settings file with all twelve keys.
    public static Path fullSettings() {
        return resource("/fixtures/settings/full.json");
    }

    /// A settings file citing an unknown key {@code unsupportedKey}.
    public static Path unknownKeySettings() {
        return resource("/fixtures/settings/unknown-key.json");
    }

    /// A settings file with the value typo {@code intRules:javaSemantic}.
    public static Path typoSettings() {
        return resource("/fixtures/settings/typo-value.json");
    }

    public static Path resource(String name) {
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
