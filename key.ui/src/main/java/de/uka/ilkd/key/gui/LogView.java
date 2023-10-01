/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.IOException;
import java.nio.file.*;
import java.util.Collections;
import java.util.List;
import javax.swing.*;
import javax.swing.text.AttributeSet;
import javax.swing.text.BadLocationException;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyleConstants;

import de.uka.ilkd.key.core.Log;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontProvider;

import net.miginfocom.layout.CC;
import net.miginfocom.swing.MigLayout;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (1/5/22)
 */
@KeYGuiExtension.Info(experimental = false, name = "Log View")
public class LogView implements KeYGuiExtension, KeYGuiExtension.StatusLine {
    private static final Logger LOGGER = LoggerFactory.getLogger(LogView.class);

    /** font to be used for log view */
    private static final IconFontProvider BOOK =
        new IconFontProvider(FontAwesomeSolid.BOOK);
    private static final KeyAction actShowLog = new ShowLogAction();
    private static final Action actOpenExternal = new OpenLogExternalAction();

    @Override
    public List<JComponent> getStatusLineComponents() {
        JButton btnShowLog = new JButton(actShowLog);
        btnShowLog.setMargin(new Insets(0, 0, 0, 0));
        return Collections.singletonList(btnShowLog);
    }

    public static class FileWatcherService implements Runnable {
        private static final Logger LOGGER = LoggerFactory.getLogger(FileWatcherService.class);
        private final Path file;
        private final Runnable callback;

        public FileWatcherService(Path fileToWatch, Runnable callback) {
            this.file = fileToWatch;
            this.callback = callback;
        }

        @Override
        public void run() {
            try (final WatchService watchService = FileSystems.getDefault().newWatchService()) {
                var watchKey =
                    file.getParent().register(watchService, StandardWatchEventKinds.ENTRY_MODIFY);
                while (!Thread.interrupted()) {
                    final WatchKey wk = watchService.take();
                    for (WatchEvent<?> event : wk.pollEvents()) {
                        // final Path changed = (Path) event.context()
                        if (wk == watchKey) {
                            callback.run();
                        }
                    }
                    // reset the key
                    wk.reset();
                }
            } catch (IOException e) {
                LOGGER.error("IO exception during listening for events", e);
            } catch (InterruptedException ignore) {
            }
        }
    }


    private static class ShowLogAction extends KeyAction {
        public ShowLogAction() {
            setTooltip("Show log");
            setIcon(BOOK.get(16));
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            JDialog dialog = new JDialog(MainWindow.getInstance(), "Log View");
            dialog.setModal(false);
            LogViewPane ui = new LogViewPane();
            dialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
            dialog.addWindowListener(new WindowAdapter() {
                @Override
                public void windowOpened(WindowEvent e) {
                    ui.onShow();
                }

                @Override
                public void windowClosed(WindowEvent e) {
                    ui.dispose();
                }

                @Override
                public void windowIconified(WindowEvent e) {
                    ui.setPause(true);
                }

                @Override
                public void windowDeiconified(WindowEvent e) {
                    ui.setPause(true);
                }
            });
            dialog.setContentPane(ui);
            dialog.setSize(800, 600);
            dialog.setLocationRelativeTo(MainWindow.getInstance());
            dialog.setVisible(true);
        }
    }

    static class LogViewPane extends JPanel {
        private static final SimpleAttributeSet ATTRIB_TIME = new SimpleAttributeSet();
        private static final AttributeSet ATTRIB_EMPTY = SimpleAttributeSet.EMPTY;
        private static final SimpleAttributeSet ATTRIB_LEVEL = new SimpleAttributeSet();
        private static final SimpleAttributeSet ATTRIB_THREAD = new SimpleAttributeSet();
        private static final SimpleAttributeSet ATTRIB_CLASS = new SimpleAttributeSet();
        private static final SimpleAttributeSet ATTRIB_FILE = new SimpleAttributeSet();
        private static final SimpleAttributeSet ATTRIB_MSG = new SimpleAttributeSet();
        private static final SimpleAttributeSet ATTRIB_EX = new SimpleAttributeSet();
        private static final AttributeSet[] STYLES = new AttributeSet[] { ATTRIB_TIME, ATTRIB_LEVEL,
            ATTRIB_THREAD, ATTRIB_CLASS, ATTRIB_FILE, ATTRIB_MSG, ATTRIB_EX };

        static {
            StyleConstants.setForeground(ATTRIB_TIME, Color.gray);
            StyleConstants.setBold(ATTRIB_LEVEL, true);
            StyleConstants.setForeground(ATTRIB_LEVEL, Color.white);
            StyleConstants.setBackground(ATTRIB_LEVEL, Color.black);
            StyleConstants.setForeground(ATTRIB_THREAD, Color.gray);
            StyleConstants.setForeground(ATTRIB_CLASS, Color.gray);
        }

        private final JTextPane txtView = new JTextPane() {
            public boolean getScrollableTracksViewportWidth() {
                final Component parent = getParent();
                return parent == null ||
                        (getUI().getPreferredSize(this).width <= parent.getSize().width);
            }
        };

        private final JCheckBox chkInfo = new JCheckBox("INFO", true);
        private final JCheckBox chkWarn = new JCheckBox("WARN", true);
        private final JCheckBox chkDebug = new JCheckBox("DEBUG", false);
        private final JCheckBox chkTrace = new JCheckBox("TRACE", false);
        private final JCheckBox chkError = new JCheckBox("ERROR", true);

        private final Thread fileWatcherServiceThread;
        private final JTextField txtMessageSearch = new JTextField();
        private final JTextField txtPackageSearch = new JTextField();

        private boolean pause = false;

        private final Path logFile = Log.getCurrentLogFile();

        public LogViewPane() {
            setLayout(new BorderLayout());

            txtView.setEditable(false);
            txtView.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));

            JPanel pFilter = new JPanel();
            pFilter.setLayout(new MigLayout());
            pFilter.setBorder(BorderFactory.createTitledBorder("Filter"));
            pFilter.add(new JLabel("Level:"));
            pFilter.add(chkError);
            pFilter.add(chkWarn);
            pFilter.add(chkInfo);
            pFilter.add(chkDebug);
            pFilter.add(chkTrace, new CC().wrap());

            pFilter.add(new JLabel("Text:"));
            pFilter.add(txtMessageSearch, new CC().span(5).growX().wrap());

            pFilter.add(new JLabel("Package (Prefix):"));
            pFilter.add(txtPackageSearch, new CC().span(5).growX());

            JPanel pActions = new JPanel();
            pActions.add(new JButton(actOpenExternal));

            add(pFilter, BorderLayout.NORTH);
            add(pActions, BorderLayout.SOUTH);
            JScrollPane scrPane = new JScrollPane(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS,
                JScrollPane.HORIZONTAL_SCROLLBAR_ALWAYS);
            scrPane.setAutoscrolls(false);
            scrPane.setViewportView(txtView);
            add(scrPane, BorderLayout.CENTER);

            FileWatcherService fileWatcherService =
                new FileWatcherService(logFile.getParent(), this::refresh);
            fileWatcherServiceThread = new Thread(fileWatcherService);
            refresh();

            ActionListener update = (e) -> refresh();
            chkTrace.addActionListener(update);
            chkDebug.addActionListener(update);
            chkInfo.addActionListener(update);
            chkWarn.addActionListener(update);
            chkError.addActionListener(update);
            txtMessageSearch.addActionListener(update);
            txtPackageSearch.addActionListener(update);
        }


        public void refresh() {
            if (pause) {
                return;
            }
            txtView.setText("");

            String pkgFilter = txtPackageSearch.getText().trim();
            boolean pkgFilterApply = pkgFilter.isEmpty();
            String msgFilter = txtMessageSearch.getText().trim();
            boolean msgFilterApply = msgFilter.isEmpty();
            boolean levelError = chkError.isSelected();
            boolean levelInfo = chkInfo.isSelected();
            boolean levelWarn = chkWarn.isSelected();
            boolean levelDebug = chkDebug.isSelected();
            boolean levelTrace = chkTrace.isSelected();

            try (var reader = Files.newBufferedReader(logFile)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    if (line.isEmpty() || line.charAt(0) == '#') {
                        continue;
                    }
                    String[] fields = line.split("[|]", STYLES.length);
                    boolean skipByMsgFilter = msgFilterApply && !fields[5].contains(msgFilter);
                    boolean skipByPkgFilter = pkgFilterApply && !fields[4].startsWith(pkgFilter);
                    boolean skipErrorLevel = !levelError && "ERROR".equals(fields[1]);
                    boolean skipWarnLevel = !levelWarn && "WARN".equals(fields[1]);
                    boolean skipInfoLevel = !levelInfo && "INFO".equals(fields[1]);
                    boolean skipDebugLevel = !levelDebug && "DEBUG".equals(fields[1]);
                    boolean skipTraceLevel = !levelTrace && "TRACE".equals(fields[1]);
                    if (!skipErrorLevel && !skipDebugLevel && !skipTraceLevel && !skipInfoLevel
                            && !skipWarnLevel && !skipByMsgFilter && !skipByPkgFilter) {
                        appendLine(fields);
                    }
                }
            } catch (IOException e) {
                LOGGER.warn("Exception while reading", e);
            }
        }

        private void appendLine(String[] fields) {
            for (int i = 0; i < fields.length; i++) {
                appendField(fields[i].replace("\\n", "\n"), STYLES[i]);
                if (i == fields.length - 1) {
                    appendField("\n", ATTRIB_EMPTY);
                } else {
                    appendField("    ", ATTRIB_EMPTY);
                }
            }
        }

        private void appendField(String txt, AttributeSet set) {
            var pos = txtView.getDocument().getEndPosition().getOffset() - 1;
            try {
                txtView.getDocument().insertString(pos, txt, set);
            } catch (BadLocationException e) {
                LOGGER.warn("Exception inserting string");
            }
        }

        public void onShow() {
            fileWatcherServiceThread.start();
        }

        public void dispose() {
            fileWatcherServiceThread.interrupt();
        }

        public void setPause(boolean flag) {
            this.pause = flag;

            flag = !flag;
            txtView.setEnabled(flag);
            chkDebug.setEnabled(flag);
            chkTrace.setEnabled(flag);
            chkError.setEnabled(flag);
            chkWarn.setEnabled(flag);
            chkInfo.setEnabled(flag);
            txtMessageSearch.setEnabled(flag);
        }
    }

    static class OpenLogExternalAction extends KeyAction {
        private static final Logger LOGGER = LoggerFactory.getLogger(OpenLogExternalAction.class);

        public OpenLogExternalAction() {
            setName("Open log externally");
            lookupAcceleratorKey();
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            final var file = Log.getCurrentLogFile().toFile();
            try {
                Desktop.getDesktop().open(file);
            } catch (IOException | UnsupportedOperationException ex) {
                LOGGER.error("Could not open editor.", ex);
                try {
                    Desktop.getDesktop().browseFileDirectory(file);
                } catch (UnsupportedOperationException ex1) {
                    LOGGER.error("Could not browse directory either.", ex1);
                }
            }
        }
    }
}
