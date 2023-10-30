/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.utilities;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (28.10.23)
 */
@KeYGuiExtension.Info(name = "Heap-Indicator",
    description = "Shows an indication of the current heap consumption in the status line of key",
    experimental = false)
public class HeapStatusExt implements KeYGuiExtension, KeYGuiExtension.StatusLine {
    @Override
    public List<JComponent> getStatusLineComponents() {
        return Collections.singletonList(new HeapStatusComponent());
    }

    private static class HeapStatusComponent extends Box {
        private static final Logger LOGGER = LoggerFactory.getLogger(HeapStatusComponent.class);

        private final JProgressBar progressBar = new JProgressBar();

        private final Action actionRunGc = new RunGcAction();

        private final Action actionShowMonitoring = new ShowMonitoringAction();


        private JPopupMenu createPopupMenu() {
            var j = new JPopupMenu("Heap");
            progressBar.addMouseListener(new MouseAdapter() {
                @Override
                public void mouseClicked(MouseEvent e) {
                    actionRunGc.actionPerformed(null);
                }
            });
            j.add(actionShowMonitoring);
            j.add(actionRunGc);
            return j;
        }

        public HeapStatusComponent() {
            super(BoxLayout.X_AXIS);
            add(progressBar);
            JPopupMenu menu = createPopupMenu();
            setComponentPopupMenu(menu);
            progressBar.setInheritsPopupMenu(true);

            update();
            var timer = new Timer(5000, evt -> update());
            timer.setRepeats(true);
            timer.start();
        }

        private void update() {
            Runtime rt = Runtime.getRuntime();
            final var mb = 1024 * 1024;

            int max = (int) (rt.maxMemory() / mb);
            int free = (int) (rt.freeMemory() / mb);
            int total = (int) (rt.totalMemory() / mb);

            progressBar.setMaximumSize(new Dimension(100, 25));

            progressBar.setMaximum(max);
            final var used = total - free;
            progressBar.setValue(used);
            progressBar.setString("%sM of %sM".formatted(used, max));
            progressBar.setStringPainted(true);
            progressBar.setToolTipText(
                "<html><table><tr><td>%s</td><td>%d MB</td></tr><tr><td>%s</td><td>%d MB</td></tr><tr><td>%s</td><td>%d MB</td></tr>"
                        .formatted(
                            "max", max,
                            "free", free,
                            "total", total));
        }

        private static class RunGcAction extends KeyAction {
            RunGcAction() {
                setName("Run Gc");
            }

            @Override
            public void actionPerformed(ActionEvent actionEvent) {
                Runtime rt = Runtime.getRuntime();
                LOGGER.info("Before GC: total {} MB, max {} MB, free {} MB",
                    rt.totalMemory() / 1048576.0,
                    rt.maxMemory() / 1048576.0,
                    rt.freeMemory() / 1048576.0);
                System.gc();
                LOGGER.info("After GC: total {} MB, max {} MB, free {} MB",
                    rt.totalMemory() / 1048576.0,
                    rt.maxMemory() / 1048576.0,
                    rt.freeMemory() / 1048576.0);
            }
        }

        private class ShowMonitoringAction extends KeyAction {
            private final String pathJConsole;

            ShowMonitoringAction() {
                setName("Open JConsole");
                pathJConsole = findJConsole();
                if (pathJConsole == null) {
                    setEnabled(false);
                    setTooltip("Could not find `jconsole`, which is shipped by some JREs/JDKs.");
                }
            }

            @Override
            public void actionPerformed(ActionEvent actionEvent) {
                long pid = ProcessHandle.current().pid();

                LOGGER.info("Execute jconsole: {} {}", pathJConsole, pid);
                try {
                    new ProcessBuilder().command(pathJConsole, String.valueOf(pid)).start();
                } catch (IOException e) {
                    JOptionPane.showConfirmDialog(HeapStatusComponent.this, e.getMessage());
                }
            }


            @Nullable
            private static String findJConsole() {
                var executableLinux = Paths.get(System.getProperty("java.home"), "bin", "jconsole");
                var executableWindows =
                    Paths.get(System.getProperty("java.home"), "bin", "jconsole.exe");

                if (Files.exists(executableLinux)) {
                    return executableLinux.toString();
                }

                if (Files.exists(executableWindows)) {
                    return executableWindows.toString();
                }
                return null;
            }
        }
    }
}
