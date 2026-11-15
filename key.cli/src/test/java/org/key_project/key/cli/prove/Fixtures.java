/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli.prove;

import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Path;
import java.util.List;

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

    /// A Java source with a syntax error whose parse diagnostic carries the source position.
    public static Path syntaxErrorJava() {
        return resource("/fixtures/syntaxerror/Bad.java");
    }

    /// A load file whose Java source declares no JML contract at all (empty selection).
    public static Path noContractsKey() {
        return resource("/fixtures/nocontracts/noContracts.key");
    }

    /// The overflow-sensitive contract used to differentiate {@code intRules} settings (E3).
    public static Path overflowKey() {
        return resource("/fixtures/overflow/overflow.key");
    }

    /**
     * The load file of the known-open three-branch {@code Size} contract: full proof search
     * closes the valid branch and leaves the two invalid branches open (§6 acceptance F2 and
     * the {@code --print-open-goals} truncation test). The scripted-proving tests use the
     * {@code /fixtures/size/} variant, whose proof starts with a single open goal.
     */
    public static Path sizeOpenKey() {
        return resource("/fixtures/size-open/size.key");
    }

    /// The load file carrying a {@code \settings} block selecting {@code intRules:javaSemantics}.
    public static Path loadFileSettingsKey() {
        return resource("/fixtures/index/loadfile-settings.key");
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

    /// The §9 acceptance settings file citing the unknown key {@code "foo"}.
    public static Path acceptanceSettings() {
        return resource("/acceptance/s.json");
    }

    /// The §8 load file whose contract cites {@code assignable bucketData[*][*];}.
    public static Path bucketStarKey() {
        return resource("/acceptance/bucket-star/index.key");
    }

    /// The §8 load file containing {@code int[][] a = new int[n][];}.
    public static Path unsizedNewKey() {
        return resource("/acceptance/unsized-new/index.key");
    }

    /// The §8 load file containing {@code int[][] a = new int[][]{{1,2}};}.
    public static Path initNewKey() {
        return resource("/acceptance/init-new/index.key");
    }

    /// All §8 bad-construct load files (one per listed construct).
    public static List<Path> badConstructKeys() {
        return List.of(bucketStarKey(), unsizedNewKey(), initNewKey());
    }

    /// One §8 bad-construct fixture: its load file and the expected exact snippet.
    public record BadConstruct(Path key, String snippet) {
    }

    /**
     * All §8 bad-construct fixtures with their expected exact snippets (one per construct
     * listed in the spec).
     *
     * @return the three fixtures: {@code bucketData[*][*]}, {@code new int[n][]},
     *         {@code new int[][]{{1,2}}}
     */
    public static List<BadConstruct> badConstructs() {
        return List.of(
            new BadConstruct(bucketStarKey(), "bucketData[*][*]"),
            new BadConstruct(unsizedNewKey(), "new int[n][]"),
            new BadConstruct(initNewKey(), "new int[][]{{1,2}}"));
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
