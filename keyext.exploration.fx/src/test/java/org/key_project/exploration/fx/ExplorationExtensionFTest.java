/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.exploration.fx;

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;
import javafx.application.Platform;
import javafx.scene.control.CheckBox;
import javafx.scene.control.Control;
import javafx.scene.control.Menu;
import javafx.scene.control.Tab;

import de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF;

import org.key_project.util.javafx.FxUtil;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Structural unit test of the {@link ExplorationExtensionF} provider of MP9.2.
 * <p>
 * The FX controls need a running toolkit; {@link Platform#startup} requires a display, so the
 * FX-dependent assertions are skipped (JUnit {@code assumeTrue}) on headless runs. The build
 * gates run with {@code DISPLAY=:92} (Xvnc) and the software pipeline.
 */
class ExplorationExtensionFTest {

    /** whether the JavaFX toolkit could be started in this JVM/display */
    private static boolean toolkitAvailable;

    @BeforeAll
    static void startToolkit() {
        // software pipeline keeps the toolkit runnable on the Xvnc display
        System.setProperty("prism.order", "sw");
        try {
            Platform.startup(() -> {
            });
            toolkitAvailable = true;
        } catch (Throwable e) {
            // headless run: the FX-dependent tests are skipped via assumeTrue
            toolkitAvailable = false;
        }
    }

    @Test
    void infoAnnotation() {
        KeYGuiExtensionF.Info info =
            ExplorationExtensionF.class.getAnnotation(KeYGuiExtensionF.Info.class);
        assertThat(info).isNotNull();
        assertThat(info.name()).isEqualTo("Exploration");
        assertThat(info.description()).contains("MP9.2");
        assertThat(info.priority()).isEqualTo(10000);
        assertThat(info.optional()).isTrue();
        assertThat(info.experimental()).isTrue();
    }

    @Test
    void serviceRegistration() throws IOException {
        // the provider must be discoverable through the FX extension SPI; the resource may be
        // shadowed by the key.ui.fx services file on the test classpath, so every copy on the
        // classpath is inspected
        Enumeration<URL> resources = ExplorationExtensionF.class.getClassLoader().getResources(
            "META-INF/services/de.uka.ilkd.key.gui.fx.extension.api.KeYGuiExtensionF");
        List<String> contents = new ArrayList<>();
        while (resources.hasMoreElements()) {
            try (InputStream in = resources.nextElement().openStream()) {
                contents.add(new String(in.readAllBytes(), StandardCharsets.UTF_8));
            }
        }
        assertThat(contents).anyMatch(
            content -> content.contains("org.key_project.exploration.fx.ExplorationExtensionF"));
    }

    @Test
    void providerInitializesWithoutMediator() {
        Assumptions.assumeTrue(toolkitAvailable);
        FxUtil.runAndWait(() -> {
            ExplorationExtensionF extension = new ExplorationExtensionF();
            // the startup hook without a mediator (headless runs) must not crash
            extension.init(null, null);
        });
    }

    @Test
    void contributesToolbarMenuStatusAndLeftPanel() {
        Assumptions.assumeTrue(toolkitAvailable);
        FxUtil.runAndWait(() -> {
            ExplorationExtensionF extension = new ExplorationExtensionF();

            // ToolbarF: the two Swing JCheckBoxes as FX check boxes
            List<Control> toolbar = extension.getToolbarControls(null, null);
            assertThat(toolbar).hasSize(2).allMatch(c -> c instanceof CheckBox);
            assertThat(((CheckBox) toolbar.get(0)).getText()).isEqualTo("Exploration Mode");
            assertThat(((CheckBox) toolbar.get(1)).getText()).isEqualTo("Hide justification");

            // LeftPanelF: exactly one west-drawer tab "Exploration Steps"
            List<Tab> tabs = extension.getLeftPanelTabs(null, null);
            assertThat(tabs).hasSize(1);
            Tab tab = tabs.get(0);
            assertThat(tab.getText()).isEqualTo("Exploration Steps");
            assertThat(tab.getContent()).isNotNull();
            assertThat(tab.isClosable()).isFalse();

            // StatusLineF: the singleton exploration-steps indicator
            List<Control> status = extension.getStatusLineControls();
            assertThat(status).hasSize(1);

            // MainMenuF: one new "Exploration" menu with the two toggles
            List<Menu> menus = extension.getMenus(null, null);
            assertThat(menus).hasSize(1);
            assertThat(menus.get(0).getText()).isEqualTo("Exploration");
            assertThat(menus.get(0).getItems()).hasSize(2);
        });
    }

    @Test
    void sequentContextItemsGuardNulls() {
        Assumptions.assumeTrue(toolkitAvailable);
        FxUtil.runAndWait(() -> {
            ExplorationExtensionF extension = new ExplorationExtensionF();
            // the facade exercises the host headless without goal/position; the sequent slot
            // must stay empty even with the exploration mode switched on
            CheckBox mode = (CheckBox) extension.getToolbarControls(null, null).get(0);
            mode.setSelected(true);
            mode.fire();
            assertThat(extension.getSequentContextItems(null, null, null)).isEmpty();
        });
    }

    @Test
    void toolbarToggleSyncsWithModel() {
        Assumptions.assumeTrue(toolkitAvailable);
        FxUtil.runAndWait(() -> {
            ExplorationExtensionF extension = new ExplorationExtensionF();
            List<Control> toolbarOnce = extension.getToolbarControls(null, null);
            List<Control> toolbarTwice = extension.getToolbarControls(null, null);
            // the toolbar hosts are cached singletons like the Swing provider's JToolBar
            assertThat(toolbarOnce.get(0)).isSameAs(toolbarTwice.get(0));
            assertThat(toolbarOnce.get(1)).isSameAs(toolbarTwice.get(1));

            CheckBox mode = (CheckBox) toolbarOnce.get(0);
            mode.fire();
            assertThat(mode.isSelected()).isTrue();
            // the second toolbar control is only enabled while the exploration mode is active
            assertThat(((CheckBox) toolbarOnce.get(1)).isDisabled()).isFalse();
        });
    }
}
