/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardWatchEventKinds;
import java.nio.file.WatchKey;
import java.nio.file.WatchService;
import java.util.Comparator;
import java.util.List;
import java.util.Optional;
import java.util.stream.Stream;
import javafx.application.Platform;
import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.CheckBox;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.TextArea;
import javafx.scene.control.TextField;
import javafx.scene.control.TitledPane;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.FlowPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;
import javafx.stage.Stage;
import javafx.stage.Window;

import de.uka.ilkd.key.settings.PathConfig;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The log viewer of the JavaFX UI — the port of the Swing {@code de.uka.ilkd.key.gui.LogView}
 * (key.ui, 325 lines). It opens a non-modal window that live-tails the current log file with
 * level/message/package filters ({@code ShowLogAction}, {@code LogView.java:88-126}; the Swing
 * status-line extension button has no FX extension SPI yet, so the FX entry point is the View
 * menu).
 * <p>
 * Ported behaviors (Swing evidence):
 * <ul>
 * <li>Log record format: the pipe-separated fields {@code date|level|thread|logger|file:line|
 * message|exception} of the Swing logback FILE appender; fields are joined with the Swing
 * spacing and embedded newlines are unescaped ({@code appendLine}, {@code LogView.java:260-269},
 * message escaping {@code :690} in the logback pattern).</li>
 * <li>Level checkboxes ERROR/WARN/INFO/DEBUG/TRACE and text/package filters re-render on change
 * ({@code :157-161, 209-216}); lines starting with {@code #} (the logback pattern header) are
 * skipped ({@code :239-241}).</li>
 * <li>Live refresh via a {@link WatchService} on the log directory ({@code
 * FileWatcherService}, {@code :54-85}), started on show and interrupted on close
 * ({@code :100-109, 280-286}); refresh is paused while the window is iconified
 * ({@code :111-119, 288-299}).</li>
 * <li>"Open log externally" via the system {@code Desktop} ({@code OpenLogExternalAction},
 * {@code :302-324}).</li>
 * </ul>
 * Documented deviations: the fields are rendered as plain text (the Swing per-field styles of
 * {@code :129-147} would need a styled text area), and the Swing package-prefix filter is
 * <b>fixed</b> in the port: its guard {@code pkgFilterApply = pkgFilter.isEmpty()}
 * ({@code :227, 244}) inverted the condition so that a non-empty package filter never filtered
 * anything.
 */
public final class LogViewF {
    private static final Logger LOGGER = LoggerFactory.getLogger(LogViewF.class);

    /** the fields of one log record (logback pattern of the Swing UI) */
    private static final int FIELD_COUNT = 7;

    private final TextArea txtView = new TextArea();
    private final CheckBox chkInfo = new CheckBox("INFO");
    private final CheckBox chkWarn = new CheckBox("WARN");
    private final CheckBox chkDebug = new CheckBox("DEBUG");
    private final CheckBox chkTrace = new CheckBox("TRACE");
    private final CheckBox chkError = new CheckBox("ERROR");
    private final TextField txtMessageSearch = new TextField();
    private final TextField txtPackageSearch = new TextField();
    private final Thread fileWatcherServiceThread;
    private final Path logFile;
    /** the root layout of the window (built in the constructor) */
    private final javafx.scene.Parent root;
    private boolean pause = false;

    /** Creates a log view bound to the given log file (public for the seam self test). */
    public LogViewF(Path logFile) {
        this.logFile = logFile;

        txtView.setEditable(false);
        txtView.getStyleClass().add("log-view-area");
        txtView.setWrapText(false);

        chkInfo.setSelected(true);
        chkWarn.setSelected(true);
        chkError.setSelected(true);

        FlowPane levelBox = new FlowPane(8, 4, chkError, chkWarn, chkInfo, chkDebug, chkTrace);
        HBox messageBox = new HBox(8, new Label("Text:"), txtMessageSearch);
        HBox.setHgrow(txtMessageSearch, javafx.scene.layout.Priority.ALWAYS);
        HBox packageBox = new HBox(8, new Label("Package (Prefix):"), txtPackageSearch);
        HBox.setHgrow(txtPackageSearch, javafx.scene.layout.Priority.ALWAYS);
        VBox filterBox = new VBox(4, new Label("Level:"), levelBox, messageBox, packageBox);
        filterBox.setPadding(new Insets(4));
        TitledPane filterPane = new TitledPane("Filter", filterBox);
        filterPane.setCollapsible(false);

        Button openExternal =
            new Button("Open log externally" + (logFile == null ? " (no log file)" : ""));
        openExternal.setOnAction(e -> openExternal());
        openExternal.setDisable(logFile == null);

        ScrollPane scroll = new ScrollPane(txtView);
        scroll.setFitToWidth(true);
        scroll.setFitToHeight(true);
        BorderPane rootPane = new BorderPane(scroll, filterPane, null,
            new javafx.scene.layout.BorderPane(openExternal), null);
        rootPane.setPadding(new Insets(4));
        root = rootPane;

        var watcher = logFile != null ? new FileWatcherService(logFile, this::refresh) : null;
        fileWatcherServiceThread =
            watcher != null ? new Thread(watcher, "fx-log-file-watcher") : null;

        for (CheckBox box : List.of(chkTrace, chkDebug, chkInfo, chkWarn, chkError)) {
            box.setOnAction(e -> refresh());
        }
        txtMessageSearch.setOnAction(e -> refresh());
        txtPackageSearch.setOnAction(e -> refresh());

        refresh();
    }

    /**
     * Opens the log view window (non-modal, 800x600, centered on the owner; Swing
     * {@code ShowLogAction.actionPerformed}, {@code LogView.java:88-126}). The file watcher is
     * started on show and stopped when the window closes.
     *
     * @param owner the owner window, may be null
     */
    public static void showInstance(Window owner) {
        LogViewF view = new LogViewF(resolveLogFile());
        Stage stage = new Stage();
        stage.setTitle("Log View");
        stage.setScene(new Scene(view.root, 800, 600));
        // pause the refresh while the window is minimized (Swing setPause on iconified)
        stage.iconifiedProperty().addListener((obs, old, iconified) -> view.setPause(iconified));
        stage.setOnCloseRequest(e -> view.dispose());
        stage.setOnHidden(e -> view.dispose());
        if (owner != null) {
            stage.setX(owner.getX() + 40);
            stage.setY(owner.getY() + 40);
        }
        stage.show();
        view.onShow();
    }

    /**
     * Resolves the current log file: the logback root "FILE" appender's file if configured (the
     * Swing {@code Log.getCurrentLogFile}, {@code Log.java:45-51}; key.ui.fx has no logback.xml
     * yet), otherwise the newest {@code key_*.log} in the log directory.
     *
     * @return the log file, or {@code null} if none can be determined
     */
    public static @Nullable Path resolveLogFile() {
        try {
            ch.qos.logback.classic.Logger root =
                (ch.qos.logback.classic.Logger) org.slf4j.LoggerFactory
                        .getLogger(org.slf4j.Logger.ROOT_LOGGER_NAME);
            if (root.getAppender("FILE") instanceof ch.qos.logback.core.FileAppender<?> file) {
                return Path.of(file.getFile());
            }
        } catch (RuntimeException e) {
            LOGGER.debug("Could not resolve the logback FILE appender", e);
        }
        Path logDir = PathConfig.currentPaths.logDirectory;
        if (Files.isDirectory(logDir)) {
            try (Stream<Path> files = Files.list(logDir)) {
                Optional<Path> newest = files
                        .filter(p -> p.getFileName() != null
                                && p.getFileName().toString().startsWith("key_")
                                && p.getFileName().toString().endsWith(".log"))
                        .max(Comparator.comparing(LogViewF::lastModified));
                return newest.orElse(null);
            } catch (IOException e) {
                LOGGER.warn("Could not list the log directory {}", logDir, e);
            }
        }
        return null;
    }

    private static long lastModified(Path path) {
        try {
            return Files.getLastModifiedTime(path).toMillis();
        } catch (IOException e) {
            return 0L;
        }
    }

    /** Starts the file watcher (Swing {@code LogViewPane.onShow}, {@code :280-282}). */
    private void onShow() {
        if (fileWatcherServiceThread != null) {
            fileWatcherServiceThread.setDaemon(true);
            fileWatcherServiceThread.start();
        }
    }

    /** Interrupts the file watcher (Swing {@code LogViewPane.dispose}, {@code :284-286}). */
    private void dispose() {
        if (fileWatcherServiceThread != null) {
            fileWatcherServiceThread.interrupt();
        }
    }

    /** Pauses/resumes the live refresh (Swing {@code LogViewPane.setPause}, {@code :288-299}). */
    private void setPause(boolean flag) {
        this.pause = flag;
    }

    /**
     * Re-reads the log file and applies the filters (Swing {@code LogViewPane.refresh},
     * {@code :220-258}). The Swing package filter bug is fixed here: a non-empty package filter
     * actually filters. Public for the seam self test.
     */
    public void refresh() {
        if (pause) {
            return;
        }
        StringBuilder buffer = new StringBuilder();
        if (logFile == null) {
            buffer.append("[NO LOG FILE FOUND - configure a logback FILE appender or check ")
                    .append(PathConfig.currentPaths.logDirectory).append("]");
        } else {
            String pkgFilter = txtPackageSearch.getText().trim();
            String msgFilter = txtMessageSearch.getText().trim();
            boolean levelError = chkError.isSelected();
            boolean levelInfo = chkInfo.isSelected();
            boolean levelWarn = chkWarn.isSelected();
            boolean levelDebug = chkDebug.isSelected();
            boolean levelTrace = chkTrace.isSelected();
            try (var reader = Files.newBufferedReader(logFile, StandardCharsets.UTF_8)) {
                String line;
                while ((line = reader.readLine()) != null) {
                    if (line.isEmpty() || line.charAt(0) == '#') {
                        continue;
                    }
                    String[] fields = line.split("[|]", FIELD_COUNT);
                    if (fields.length < FIELD_COUNT) {
                        continue;
                    }
                    boolean skipByMsgFilter = !msgFilter.isEmpty()
                            && !fields[5].contains(msgFilter);
                    boolean skipByPkgFilter = !pkgFilter.isEmpty()
                            && !fields[4].startsWith(pkgFilter);
                    boolean skipErrorLevel = !levelError && "ERROR".equals(fields[1]);
                    boolean skipWarnLevel = !levelWarn && "WARN".equals(fields[1]);
                    boolean skipInfoLevel = !levelInfo && "INFO".equals(fields[1]);
                    boolean skipDebugLevel = !levelDebug && "DEBUG".equals(fields[1]);
                    boolean skipTraceLevel = !levelTrace && "TRACE".equals(fields[1]);
                    if (!skipErrorLevel && !skipDebugLevel && !skipTraceLevel && !skipInfoLevel
                            && !skipWarnLevel && !skipByMsgFilter && !skipByPkgFilter) {
                        appendLine(buffer, fields);
                    }
                }
            } catch (IOException e) {
                LOGGER.warn("Exception while reading", e);
            }
        }
        String content = buffer.toString();
        double scroll = txtView.getScrollTop();
        txtView.setText(content);
        // live tail: keep the view at the previous scroll offset or jump to the end on append
        txtView.setScrollTop(content.isEmpty() ? 0 : Math.max(scroll, 0));
    }

    /**
     * Self-test hook: reports whether the rendered (filtered) view contains the given text.
     *
     * @param needle the expected log text
     * @return a {@code "... verification: PASS/FAIL (...)"} report line
     */
    public String verifyContains(String needle) {
        boolean pass = txtView.getText().contains(needle);
        return "LogViewF contains '" + needle + "': " + (pass ? "PASS" : "FAIL");
    }

    /** Appends one record with the Swing field spacing ({@code LogView.java:260-269}). */
    private static void appendLine(StringBuilder buffer, String[] fields) {
        for (int i = 0; i < fields.length; i++) {
            buffer.append(fields[i].replace("\\n", "\n"));
            if (i == fields.length - 1) {
                buffer.append('\n');
            } else {
                buffer.append("    ");
            }
        }
    }

    /** Opens the log file with the system Desktop (Swing {@code :302-324}). */
    private void openExternal() {
        if (logFile == null) {
            return;
        }
        try {
            java.awt.Desktop.getDesktop().open(logFile.toFile());
        } catch (IOException | UnsupportedOperationException ex) {
            LOGGER.error("Could not open editor.", ex);
        }
    }

    /**
     * The file watcher of the Swing {@code LogView.FileWatcherService} ({@code :54-85}): the
     * callback runs on every modification event of the watched directory.
     */
    public static class FileWatcherService implements Runnable {
        private static final Logger LOGGER =
            LoggerFactory.getLogger(FileWatcherService.class);
        private final Path file;
        private final Runnable callback;

        public FileWatcherService(Path fileToWatch, Runnable callback) {
            this.file = fileToWatch;
            this.callback = callback;
        }

        @Override
        public void run() {
            try (WatchService watchService = java.nio.file.FileSystems.getDefault()
                    .newWatchService()) {
                var watchKey = file.getParent().register(watchService,
                    StandardWatchEventKinds.ENTRY_MODIFY);
                while (!Thread.interrupted()) {
                    WatchKey wk = watchService.take();
                    if (wk == watchKey) {
                        Platform.runLater(callback);
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
}
