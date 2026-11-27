/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.settings;

import java.nio.file.Path;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Tests for {@link GeneralSettings}, in particular the persistence of the last used file chooser
 * path.
 */
class GeneralSettingsTest {

    @TempDir
    Path tempDir;

    @Test
    void lastUsedPathSurvivesConfigurationRoundTrip() {
        var settings = new GeneralSettings();
        var selectedFile = tempDir.resolve("proof.proof").toFile();
        settings.setLastUsedPath(selectedFile);

        var configuration = new Configuration();
        settings.writeSettings(configuration);

        assertThat(configuration.getString(GeneralSettings.LAST_USED_PATH))
                .isEqualTo(selectedFile.getAbsolutePath());

        var reloaded = new GeneralSettings();
        reloaded.readSettings(configuration);
        assertThat(reloaded.getLastUsedPath()).isEqualTo(selectedFile);
    }

    @Test
    void ensureFolderResolvesParentOfFileThatDoesNotExist() {
        var settings = new GeneralSettings();
        settings.setLastUsedPath(tempDir.resolve("new.proof").toFile());

        assertThat(settings.getLastUsedPathEnsureFolder()).isEqualTo(tempDir.toFile());
    }

    @Test
    void ensureFolderKeepsDirectory() {
        var settings = new GeneralSettings();
        settings.setLastUsedPath(tempDir.toFile());

        assertThat(settings.getLastUsedPathEnsureFolder()).isEqualTo(tempDir.toFile());
    }
}
