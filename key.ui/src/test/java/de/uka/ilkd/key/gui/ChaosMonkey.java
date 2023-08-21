/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.event.ActionEvent;
import java.awt.event.WindowEvent;
import java.lang.ref.Reference;
import java.util.ArrayList;
import java.util.Objects;
import java.util.Random;
import java.util.Set;
import java.util.stream.Collectors;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.actions.EditMostRecentFileAction;
import de.uka.ilkd.key.gui.actions.KeYProjectHomepageAction;
import de.uka.ilkd.key.gui.actions.LemmaGenerationAction;
import de.uka.ilkd.key.gui.keyshortcuts.KeyStrokeManager;
import de.uka.ilkd.key.settings.ProofIndependentSettings;

import org.key_project.util.java.SwingUtil;

import bibliothek.gui.dock.dockable.AbstractDockable;
import org.junit.jupiter.api.*;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Random testing of the UI. Will click random buttons and perform random actions.
 *
 * @author Arne Keller
 */
final class ChaosMonkey {

    private static final Logger LOGGER = LoggerFactory.getLogger(ChaosMonkey.class);

    private static final Set<String> BANNED_ACTIONS =
        Set.of("Open the last opened file with the default external editor", "Show log");
    private static final Set<Class<?>> BANNED_KEY_ACTIONS =
        Set.of(LemmaGenerationAction.ProveKeYTaclets.class,
            KeYProjectHomepageAction.class,
            EditMostRecentFileAction.class,
            LogView.OpenLogExternalAction.class);
    /**
     * Actions that should not be done, specified by class name.
     * Use this if the action is a private class!
     */
    private static final Set<String> BANNED_KEY_ACTIONS_BY_CLASS_NAME = Set.of(
        "de.uka.ilkd.key.gui.help.HelpFacade$OpenHelpAction");

    private static boolean detectedError = false;

    @Test
    @Disabled
    void clickAllTheButtons() {
        new Thread(ChaosMonkey::click, "ChaosMonkey").start();

        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                .setShowLoadExamplesDialog(false);

        Main.main(
            "--examples ../key.ui/examples ../key.ui/examples/firstTouch/01-Agatha/project.key"
                    .split(" "));
        MainWindow mw = MainWindow.getInstance();
        mw.setSize(800, 600);
        mw.setLocation(0, 0);

        try {
            while (true) {
                Thread.sleep(100000);
            }
        } catch (InterruptedException e) {
        }
    }

    static void click() {
        // wishlist:
        // - interaction with dialogs/popup menus besides closing them
        try {
            Thread.sleep(3000);
        } catch (InterruptedException e) {
            return;
        }
        MainWindow mw = MainWindow.getInstance();
        KeYMediator mediator = mw.getMediator();
        Random rand = new Random();
        try {
            while (!detectedError) {
                // wait for automode to finish
                mediator.getUI().getProofControl().waitWhileAutoMode();

                // close any dialogs and popup menus
                var windows = SwingUtil.getAllOpenWindows();
                for (var window : windows) {
                    if (window instanceof MainWindow || !window.isVisible()) {
                        continue;
                    }
                    String title = window instanceof JDialog ? ((JDialog) window).getTitle()
                            : window.getClass().toString();
                    LOGGER.info("closing: {}", title);
                    SwingUtilities.invokeLater(() -> {
                        window.dispatchEvent(new WindowEvent(window, WindowEvent.WINDOW_CLOSING));
                    });
                    Thread.sleep(500);
                }
                var popups = SwingUtil.getPopups();
                for (var popup : popups) {
                    LOGGER.info("hiding popup menu");
                    popup.setVisible(false);
                    Thread.sleep(250);
                }

                // now, find a random button to press >:)
                var buttons = SwingUtil.findAllComponents(MainWindow.getInstance(), JButton.class);
                var keyActions = KeyStrokeManager.getAllActions()
                        .stream().map(Reference::get).filter(Objects::nonNull)
                        .collect(Collectors.toSet());
                var allMenuItems =
                    SwingUtil.findAllComponents(MainWindow.getInstance(), JMenuItem.class);
                var actions = new ArrayList<>();
                actions.addAll(buttons);
                actions.addAll(keyActions);
                for (var menuItem : allMenuItems) {
                    if (menuItem.getAction() != null && keyActions.contains(menuItem.getAction())) {
                        continue;
                    }
                    if (!menuItem.isEnabled() || (menuItem instanceof JMenu)) {
                        continue;
                    }
                    actions.add(menuItem);
                }
                var foundButton = false;
                LOGGER.info("monkey chooses from {} buttons, actions and menu items ...",
                    actions.size());
                for (int i = 0; i < 100; i++) {
                    int actionIdx = rand.nextInt(actions.size());
                    var action = actions.get(actionIdx);
                    if (action instanceof JButton) {
                        JButton button = (JButton) action;
                        // only enabled buttons
                        // (the "Show log" button is broken in test cases)
                        if (!button.isEnabled() || (button.getToolTipText() != null
                                && BANNED_ACTIONS.contains(button.getToolTipText()))) {
                            continue;
                        }
                        LOGGER.info("monkey clicks on {} {} {}", button.getClass(),
                            button.getName(), button.getToolTipText());
                        var hierarchy = new ArrayList<>();
                        var container = button.getParent();
                        while (container != null) {
                            hierarchy.add(container);
                            container = container.getParent();
                        }
                        for (var x : hierarchy) {
                            if (x instanceof AbstractDockable) {
                                AbstractDockable c = (AbstractDockable) x;
                                LOGGER.info(" {}", c.getTitleText());
                            } else {
                                LOGGER.info(" {}", x);
                            }
                        }
                        SwingUtilities.invokeLater(() -> {
                            try {
                                button.doClick();
                            } catch (Exception e) {
                                LOGGER.error("detected uncaught exception ", e);
                                detectedError = true;
                            }
                        });
                        foundButton = true;
                        break;
                    } else if (action instanceof Action) {
                        Action keyAction = (Action) action;
                        if (!keyAction.isEnabled()
                                || BANNED_KEY_ACTIONS.contains(keyAction.getClass())
                                || BANNED_KEY_ACTIONS_BY_CLASS_NAME
                                        .contains(keyAction.getClass().getName())) {
                            continue;
                        }
                        LOGGER.info("performing action {}", keyAction);
                        SwingUtilities.invokeLater(() -> {
                            try {
                                Object source = keyAction;
                                var menuItems = SwingUtil.findAllComponents(mw, JMenuItem.class);
                                for (var menuItem : menuItems) {
                                    if (menuItem.getAction() == keyAction) {
                                        source = menuItem;
                                        break;
                                    }
                                }
                                keyAction.actionPerformed(new ActionEvent(source, 0, ""));
                            } catch (Exception e) {
                                LOGGER.error("detected uncaught exception ", e);
                                detectedError = true;
                            }
                        });
                        foundButton = true;
                        break;
                    } else if (action instanceof JMenuItem) {
                        var menuItem = (JMenuItem) action;
                        LOGGER.info("performing menu item {}", menuItem.getText());
                        SwingUtilities.invokeLater(() -> {
                            try {
                                menuItem.doClick(50);
                            } catch (Exception e) {
                                LOGGER.error("detected uncaught exception ", e);
                                detectedError = true;
                            }
                        });
                        foundButton = true;
                        break;
                    }
                }
                if (!foundButton) {
                    LOGGER.error("chaos monkey failed to find an enabled button!");
                    break;
                }
                Thread.sleep(1000);
            }
        } catch (Exception e) {
            LOGGER.error("chaos monkey failed (in unexpected way)! ", e);
        }
    }
}
