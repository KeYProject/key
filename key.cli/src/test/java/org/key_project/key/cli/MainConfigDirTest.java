/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.settings.PathConfig;

import org.key_project.key.cli.prove.Fixtures;

import org.checkerframework.checker.nullness.qual.EnsuresNonNull;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * End-to-end tests for the {@code --config-dir} option (§5.1, Task 4.3): the pre-scan of the
 * raw arguments for the option, the redirection of KeY's user-persistence directory into the
 * chosen base, and the acceptance of a load-file {@code \settings} block (spec source 3).
 */
class MainConfigDirTest {

    // set in @BeforeAll quietLogs(), which is annotated @EnsuresNonNull for these fields
    @SuppressWarnings("nullness:initialization.static.field.uninitialized")
    private static Path tmpHome;
    @SuppressWarnings("nullness:initialization.static.field.uninitialized")
    private static Path cfgDir;

    @BeforeAll
    @EnsuresNonNull({ "tmpHome", "cfgDir" })
    static void quietLogs() throws IOException {
        Log.configureLogging(Verbosity.ERROR);
        Path base = Files.createTempDirectory("config-dir-test");
        tmpHome = base.resolve("home");
        cfgDir = base.resolve("cfg");
        Files.createDirectories(tmpHome);
        Files.createDirectories(cfgDir);
    }

    @AfterEach
    @SuppressWarnings("nullness:clear.system.property") // deliberate cleanup of the redirection
    void clearKeyHomeProperty() {
        System.clearProperty(PathConfig.KEY_HOME_PROPERTY);
    }

    @Test
    @SuppressWarnings("nullness:argument.type.incompatible") // getProperty is nullable by design
    void preScanConfigDirSetsTheKeyHomeSystemProperty() {
        Main.preScanConfigDir(new String[] { "--config-dir", cfgDir.toString() });

        assertThat(System.getProperty(PathConfig.KEY_HOME_PROPERTY)).isEqualTo(cfgDir.toString());

        // the "--config-dir=<DIR>" spelling is accepted too
        Path other = cfgDir.resolveSibling("other-cfg");
        Main.preScanConfigDir(new String[] { "--config-dir=" + other });
        assertThat(System.getProperty(PathConfig.KEY_HOME_PROPERTY)).isEqualTo(other.toString());
    }

    @Test
    @SuppressWarnings("nullness:argument.type.incompatible") // getProperty is nullable by design
    void preScanDoesNothingWithoutTheOption() {
        // the pre-scan must not set the property when no --config-dir is present
        Main.preScanConfigDir(new String[] { "list", "some.key" });
        assertThat(System.getProperty(PathConfig.KEY_HOME_PROPERTY)).isNull();
    }

    /**
     * The E2-spirit determinism test: two fresh subprocesses listing the same file with the same
     * {@code --config-dir} produce byte-identical stdout, the config files land inside the chosen
     * base (not {@code ~/.key}), and the real {@code user.home} is left untouched.
     *
     * @throws Exception if the fixture cannot be resolved or a subprocess fails
     */
    @Test
    @Timeout(300)
    void configDirRedirectsPersistenceAndKeepsOutputDeterministic() throws Exception {
        // run twice: the FIRST run writes the config, the SECOND proves existing config is
        // reused without changing stdout.
        String first = listOn(new String[] {});
        String second = listOn(new String[] {});
        assertThat(second).isEqualTo(first);

        // the chosen base directory holds the KeY config files under v<major>.<minor>.
        Path versioned = configVersionPath(cfgDir);
        try (var stream = Files.list(versioned)) {
            assertThat(stream.count())
                    .as("config files are written into <cfg>/v<major>.<minor>").isGreaterThan(0);
        }

        // ... and the destined user.home was not used: no ~/.key was created there.
        assertThat(Files.exists(tmpHome.resolve(".key")))
                .as("the real user.home's .key must remain untouched").isFalse();
    }

    /**
     * The load-file {@code \settings}{@code ()} block (spec source 3) is accepted and its choice
     * is visible in the loaded proof's settings.
     *
     * @throws Exception if the fixture cannot be loaded
     */
    @Test
    @Timeout(120)
    void loadFileSettingsBlockIsAcceptedAndReflected() throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> environment =
            KeYEnvironment.load(Fixtures.loadFileSettingsKey());
        try {
            String intRules = environment.getLoadedProof().getSettings().getChoiceSettings()
                    .getDefaultChoices().get("intRules");
            assertThat(intRules == null ? "<absent>" : intRules)
                    .isEqualTo("intRules:javaSemantics");
        } finally {
            environment.dispose();
        }
    }

    private static String listOn(String[] extraArgs) throws Exception {
        Path index = Fixtures.indexKey();
        List<String> command = new ArrayList<>();
        command.add(javaBin());
        command.add("-Duser.home=" + tmpHome);
        command.add("-cp");
        command.add(System.getProperty("java.class.path"));
        command.add(Main.class.getName());
        command.add("--config-dir");
        command.add(cfgDir.toString());
        for (String arg : extraArgs) {
            command.add(arg);
        }
        command.add("list");
        command.add(index.toString());

        Process process = new ProcessBuilder(command).redirectErrorStream(false).start();
        String out = new String(process.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
        String err = new String(process.getErrorStream().readAllBytes(), StandardCharsets.UTF_8);
        boolean finished = process.waitFor(240, TimeUnit.SECONDS);
        if (!finished) {
            process.destroyForcibly();
            throw new AssertionError("subprocess did not terminate");
        }
        assertThat(process.exitValue()).as("stderr after subprocess: %s", err).isZero();
        return out;
    }

    @SuppressWarnings("nullness:dereference.of.nullable") // Stream<Path> elements are never null
    private static Path configVersionPath(Path base) {
        try (var stream = Files.list(base)) {
            return stream.filter(Files::isDirectory)
                    .filter(p -> p.getFileName().toString().matches("v\\d+\\.\\d+"))
                    .findFirst().orElseThrow();
        } catch (IOException e) {
            throw new AssertionError("no versioned config directory in " + base, e);
        }
    }

    private static String javaBin() {
        return Path.of(System.getProperty("java.home"), "bin", "java").toString();
    }
}
