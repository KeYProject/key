/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.net.URI;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import javafx.application.Platform;
import javafx.geometry.Insets;
import javafx.geometry.Orientation;
import javafx.scene.control.ButtonType;
import javafx.scene.control.CheckBox;
import javafx.scene.control.Dialog;
import javafx.scene.control.DialogPane;
import javafx.scene.control.Label;
import javafx.scene.control.ListView;
import javafx.scene.control.SplitPane;
import javafx.scene.control.TextArea;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.stage.Window;
import javafx.util.Duration;

import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.util.ExceptionTools;
import de.uka.ilkd.key.util.parsing.BuildingExceptions;

import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.parsing.Location;
import org.key_project.util.parsing.Position;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The central error/warning dialog of the JavaFX UI: the port of the Swing
 * {@code de.uka.ilkd.key.gui.IssueDialog} (key.ui, 877 lines). It shows a list of issues
 * (exceptions or non-critical specification warnings) with a source preview of the selected
 * issue and, for critical exceptions, an optional stack-trace pane ("Show Details").
 * <p>
 * Ported behaviors (Swing evidence):
 * <ul>
 * <li>Static entry points {@code showExceptionDialog} ({@code IssueDialog.java:582-594}) and
 * {@code showWarningsIfNecessary} ({@code :602-619}) with the session-wide "Ignore these
 * warnings" set ({@code ignoredWarnings}, {@code :92}, applied in {@code accept}
 * {@code :658-663}).</li>
 * <li>Exception message/location extraction via the core {@link ExceptionTools#getMessages}
 * ({@code extractMessage}, {@code :635-655}); the full stack trace is the issue's detail text
 * ({@code :636-644}).</li>
 * <li>Issue list sorted by location ({@code :244-245}); selection updates the source preview,
 * the location labels and the stack trace ({@code updatePreview}, {@code :665-729},
 * {@code updateStackTrace}, {@code :747-749}); the source file is read from the issue's
 * location URI with a per-dialog cache ({@code :688-702}); the error position is mapped from
 * the 1-based line/column to an offset and marked in the preview ({@code :716-723},
 * {@code :766-795}).</li>
 * <li>Modal dialog with a default OK button ({@code :536}, {@code :544}).</li>
 * </ul>
 * Documented deviations: no HTML rendering (issue texts and the URL-click decoration of
 * {@code decorateHTML}, {@code :183-208}, are shown as plain text — URLs are still visible),
 * no syntax highlighting/lexer in the source preview (plain monospace text), no line-number
 * column, and the "Edit File"/"Send Feedback" buttons of the Swing dialog
 * ({@code :513-534}) are deferred (they need the source view action and the feedback
 * infrastructure). The scroll-to-error position is approximated via the {@link TextArea}'s
 * scroll properties. <b>Behavioral deviation</b>: the dialog is shown with {@link #show}
 * (non-blocking) instead of the Swing blocking {@code showAndWait} — a modal
 * {@code showAndWait} on the FX Application Thread can deadlock callers that join on that
 * thread; application modality is preserved, so the other windows are blocked while it is
 * open.
 */
public final class IssueDialogF {
    private static final Logger LOGGER = LoggerFactory.getLogger(IssueDialogF.class);

    /** Default text for critical issues (runtime exceptions), Swing {@code :80}. */
    private static final String CRITICAL_ISSUE = "The following exception occurred:";
    /** Default text for non-critical issues (JML specification warnings), Swing {@code :84-86}. */
    private static final String NON_CRITICAL_ISSUE = String.format(
        "The following non-fatal problems occurred when translating your %s specifications:",
        SLEnvInput.getLanguage());

    /** warnings which have been marked to be ignored by the user (in this KeY run) */
    private static final Set<IssueEntry> ignoredWarnings = new HashSet<>();

    /** the most recently created dialog (self-test hook, see {@link #getLastDialog()}) */
    private static @Nullable IssueDialogF lastDialog;

    /** Severity of an issue (Swing {@code PositionedIssueString.Kind}). */
    public enum Kind {
        ERROR, WARNING, INFO
    }

    /**
     * One issue shown by this dialog — the FX-side equivalent of the Swing
     * {@code PositionedIssueString} (which lives in {@code key.ui} and cannot be reused).
     *
     * @param text the issue text
     * @param location the source location, may be {@code Location.UNDEFINED}
     * @param additionalInfo additional information such as a stack trace
     * @param kind the severity
     */
    public record IssueEntry(String text, Location location, String additionalInfo, Kind kind) {
        public IssueEntry(String text) {
            this(text, Location.UNDEFINED, "", Kind.ERROR);
        }

        public IssueEntry(PositionedString ps, String additionalInfo, Kind kind) {
            this(ps.text, ps.location, additionalInfo, kind);
        }
    }

    private final Dialog<Void> dialog;
    private final ListView<IssueEntry> listWarnings;
    private final TextArea txtSource = new TextArea();
    private final TextArea txtStacktrace = new TextArea();
    private final Label fileField = new Label();
    private final Label lineField = new Label();
    private final Label columnField = new Label();
    private final CheckBox chkIgnoreWarnings =
        new CheckBox("Ignore these warnings for the current session");
    private final CheckBox chkDetails = new CheckBox("Show Details");
    private final BorderPane stacktracePanel = new BorderPane();
    private final Map<URI, String> fileContentsCache = new HashMap<>();
    private final boolean critical;
    private final List<IssueEntry> issues;

    private IssueDialogF(Window owner, String title, String head, Collection<IssueEntry> issueSet,
            boolean critical) {
        this.critical = critical;
        this.issues = new ArrayList<>(issueSet);
        this.issues.sort(Comparator.comparing(IssueEntry::location));
        lastDialog = this;

        dialog = new Dialog<>();
        dialog.setTitle(title);
        if (owner != null) {
            dialog.initOwner(owner);
        }
        dialog.setResizable(true);

        listWarnings = new ListView<>();
        listWarnings.getItems().setAll(issues);
        listWarnings.getStyleClass().add("issue-dialog-list");
        listWarnings.getSelectionModel().selectedItemProperty()
                .addListener((obs, old, issue) -> updatePreview(issue));
        listWarnings.setCellFactory(view -> new javafx.scene.control.ListCell<>() {
            private final Label label = new Label();

            {
                label.setWrapText(true);
                label.getStyleClass().add("issue-dialog-cell");
                setGraphic(null);
                setContentDisplay(javafx.scene.control.ContentDisplay.GRAPHIC_ONLY);
            }

            @Override
            protected void updateItem(IssueEntry item, boolean empty) {
                super.updateItem(item, empty);
                if (empty || item == null) {
                    setText(null);
                    label.setText(null);
                } else {
                    label.setText(item.text());
                    setGraphic(label);
                }
            }
        });

        // source preview with the location labels (Swing createSourcePanel, :498-572)
        txtSource.setEditable(false);
        txtSource.getStyleClass().add("issue-dialog-source");
        txtSource.setWrapText(false);
        txtStacktrace.setEditable(false);
        txtStacktrace.getStyleClass().add("issue-dialog-source");
        stacktracePanel.setStyle("-fx-border-color: -key-border; -fx-border-width: 1 0 0 0;");
        Label stackTitle = new Label("Stack Trace");
        stackTitle.getStyleClass().add("dialog-section-title");
        stacktracePanel.setTop(stackTitle);
        stacktracePanel.setCenter(txtStacktrace);
        stacktracePanel.setVisible(false);
        stacktracePanel.setManaged(false);

        fileField.getStyleClass().add("issue-dialog-location");
        VBox sourcePanel = new VBox(4, new HBox(12, fileField, lineField, columnField), txtSource);
        VBox.setVgrow(txtSource, Priority.ALWAYS);

        SplitPane splitCenter = new SplitPane(listWarnings, sourcePanel);
        splitCenter.setOrientation(Orientation.VERTICAL);
        splitCenter.setDividerPositions(0.35);
        VBox content = new VBox(6, new Label(head), splitCenter);
        content.setPadding(new Insets(6));
        if (!critical) {
            content.getChildren().add(chkIgnoreWarnings);
        }
        chkDetails.selectedProperty().addListener((obs, old, selected) -> {
            stacktracePanel.setVisible(selected);
            stacktracePanel.setManaged(selected);
            // the issue with a stack trace drives the pane content; re-sync
            updateStackTrace(listWarnings.getSelectionModel().getSelectedItem());
        });
        VBox.setVgrow(splitCenter, Priority.ALWAYS);
        content.getChildren().add(chkDetails);
        content.getChildren().add(stacktracePanel);

        DialogPane pane = dialog.getDialogPane();
        pane.getStyleClass().add("issue-dialog");
        pane.setContent(content);
        pane.getButtonTypes().setAll(ButtonType.OK);
        dialog.setResultConverter(button -> {
            accept();
            return null;
        });

        // "Show Details" only makes sense with a stack trace (Swing :347-364)
        chkDetails.setDisable(issues.stream().allMatch(it -> it.additionalInfo().isEmpty()));
        chkIgnoreWarnings.setSelected(false);
        if (!issues.isEmpty()) {
            listWarnings.getSelectionModel().select(0);
        }
        updatePreview(listWarnings.getSelectionModel().getSelectedItem());
    }

    /**
     * Shows the dialog with a single exception. The stacktrace is extracted and can optionally
     * be shown in the dialog (Swing {@code showExceptionDialog}, {@code IssueDialog.java:582-594}).
     * Must be called on the FX Application Thread; other threads are marshalled.
     * <p>
     * Important: make sure to also log the exception before showing the dialog!
     *
     * @param owner the owner of the dialog (will be blocked)
     * @param exception the exception to display
     */
    public static void showExceptionDialog(Window owner, Throwable exception) {
        if (!Platform.isFxApplicationThread()) {
            Platform.runLater(() -> showExceptionDialog(owner, exception));
            return;
        }
        if (exception instanceof BuildingExceptions be) {
            be.getErrors().forEach(it -> LOGGER.info("Error", it));
        }
        createExceptionDialog(owner, exception).showAndWait();
    }

    /**
     * Creates (but does not show) the exception dialog; used by the self test, which needs to
     * auto-close the dialog.
     *
     * @param owner the owner of the dialog
     * @param exception the exception to display
     * @return the dialog, not yet shown
     */
    public static IssueDialogF createExceptionDialog(Window owner, Throwable exception) {
        return new IssueDialogF(owner, "Error", CRITICAL_ISSUE, extractMessage(exception), true);
    }

    /**
     * Shows the dialog of a set of (non-critical) parser warnings (Swing
     * {@code showWarningsIfNecessary}, {@code IssueDialog.java:602-619}); warnings the user
     * chose to ignore for this session are filtered out.
     *
     * @param owner the owner of the dialog (will be blocked)
     * @param warnings the set of warnings, will be sorted by file when displaying
     */
    public static void showWarningsIfNecessary(Window owner,
            ImmutableSet<PositionedString> warnings) {
        List<IssueEntry> issues = new ArrayList<>();
        for (PositionedString ps : warnings.toSet()) {
            IssueEntry entry = new IssueEntry(ps, "", Kind.WARNING);
            if (!ignoredWarnings.contains(entry)) {
                issues.add(entry);
            }
        }
        // do not show warnings dialog if all warnings are ignored (Swing :606-607)
        if (!issues.isEmpty()) {
            new IssueDialogF(owner, SLEnvInput.getLanguage() + " warning(s)", NON_CRITICAL_ISSUE,
                issues, false).showAndWait();
        }
    }

    /**
     * Shows the issue dialog for arbitrary issues with the "critical" styling (Swing
     * {@code WindowUserInterfaceControl.showIssueDialog}, {@code :633-641}).
     *
     * @param owner the owner of the dialog
     * @param title the dialog title
     * @param issues the issues to show
     */
    public static void showIssues(Window owner, String title,
            Collection<PositionedString> issues) {
        Set<IssueEntry> entries = issues.stream()
                .map(it -> new IssueEntry(it, "", Kind.ERROR))
                .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new));
        new IssueDialogF(owner, title, CRITICAL_ISSUE, entries, true).showAndWait();
    }

    /**
     * Turns a thrown exception into the set of issues shown by this dialog (message, source
     * location and the full stack trace as detail) — Swing {@code extractMessage}
     * ({@code IssueDialog.java:635-655}); the extraction itself is delegated to the core
     * {@link ExceptionTools#getMessages}.
     *
     * @param exception the exception to extract the data from
     * @return one issue per contained problem
     */
    public static Set<IssueEntry> extractMessage(Throwable exception) {
        String stackTrace;
        try (StringWriter sw = new StringWriter(); PrintWriter pw = new PrintWriter(sw)) {
            exception.printStackTrace(pw);
            stackTrace = sw.toString();
        } catch (IOException e) {
            stackTrace = "";
        }

        Set<IssueEntry> result = new LinkedHashSet<>();
        for (PositionedString ps : ExceptionTools.getMessages(exception)) {
            result.add(new IssueEntry(ps, stackTrace, Kind.ERROR));
        }
        if (result.isEmpty()) {
            result.add(new IssueEntry("Constructing the error message failed!"));
        }
        return result;
    }

    /** The OK action: remember ignored warnings and close (Swing {@code accept}, :658-663). */
    private void accept() {
        if (!critical && chkIgnoreWarnings.isSelected()) {
            ignoredWarnings.addAll(issues);
        }
        dialog.close();
    }

    /**
     * Shows the dialog non-blockingly and closes it after the given delay — a helper for the
     * seam self test, which cannot dismiss a modal dialog interactively.
     *
     * @param autoClose the delay after which the dialog closes itself
     */
    public void showAndCloseAfter(Duration autoClose) {
        dialog.show();
        javafx.animation.PauseTransition pause = new javafx.animation.PauseTransition(autoClose);
        pause.setOnFinished(ignored -> dialog.close());
        pause.play();
    }

    /**
     * Updates the source preview and the location labels for the selected issue (Swing
     * {@code updatePreview}, {@code IssueDialog.java:665-729}).
     *
     * @param issue the selected issue, may be null
     */
    private void updatePreview(@Nullable IssueEntry issue) {
        if (issue == null) {
            fileField.setText("");
            lineField.setText("");
            columnField.setText("");
            txtSource.setText("");
            updateStackTrace(null);
            return;
        }
        updateStackTrace(issue);
        Location location = issue.location();
        Position pos = location.getPosition();
        columnField.setText("Column: " + pos.column());
        lineField.setText("Line: " + pos.line());

        URI uri = location.getFileURI().orElse(null);
        if (uri == null) {
            fileField.setText("");
            txtSource.setText("[SOURCE COULD NOT BE LOADED]");
            return;
        }
        if (uri.getScheme() == null) {
            uri = URI.create("file:" + uri.getPath());
        }
        fileField.setText("URL: " + uri);
        final URI uriKey = uri;
        String source = fileContentsCache.computeIfAbsent(uriKey, fn -> {
            try {
                return readFrom(uriKey);
            } catch (IOException e) {
                LOGGER.debug("Unknown IOException!", e);
                return "[SOURCE COULD NOT BE LOADED]\n" + e.getMessage();
            }
        });
        txtSource.setText(source);

        // mark the error position: map the 1-based position to an offset and select the word at
        // the offset (Swing addHighlights, :766-795; the offset mapping mirrors
        // getOffsetFromLineColumn, :823-830)
        if (!pos.isNegative() && !source.isEmpty()) {
            int offset = offsetFromLineColumn(source, pos);
            int end = offset;
            if (offset < source.length()
                    && Character.isJavaIdentifierPart(source.charAt(offset))) {
                while (end < source.length()
                        && Character.isJavaIdentifierPart(source.charAt(end))) {
                    end++;
                }
            } else if (offset < source.length()
                    && !Character.isWhitespace(source.charAt(offset))) {
                end = offset + 1;
            }
            txtSource.selectRange(offset, Math.min(end, source.length()));
            scrollToOffset(offset);
        } else {
            txtSource.deselect();
        }
    }

    /** Shows the additional information (e.g. the stack trace) (Swing :747-749). */
    private void updateStackTrace(@Nullable IssueEntry issue) {
        txtStacktrace.setText(issue == null ? "" : issue.additionalInfo());
    }

    /**
     * Approximate scroll-to-error: the {@link TextArea} exposes only scroll offsets, so the
     * pixel position of the error line is estimated from the line number and the font metrics
     * (Swing scrolls exactly via {@code scrollRectToVisible}, {@code IssueDialog.java:736-745}).
     */
    private void scrollToOffset(int offset) {
        String before = txtSource.getText(0, Math.min(offset, txtSource.getLength()));
        int line = before.split("\n", -1).length - 1;
        double lineHeight = Math.max(txtSource.getFont().getSize() * 1.4, 1.0);
        Platform.runLater(() -> txtSource.setScrollTop(Math.max(0, line * lineHeight - 50)));
    }

    /**
     * Maps a 1-based {@link Position} to a character offset in {@code source} (Swing
     * {@code getOffsetFromLineColumn}, {@code IssueDialog.java:823-830}; the line model is the
     * plain-text line split here).
     *
     * @param source the source text shown in the preview
     * @param pos a 1-based position
     * @return the character offset of that position within {@code source}
     */
    static int offsetFromLineColumn(String source, Position pos) {
        String[] lines = source.split("\n", -1);
        int line = Math.max(0, Math.min(pos.line() - 1, lines.length - 1));
        int column = Math.max(0, pos.column() - 1);
        int offset = 0;
        for (int i = 0; i < line; i++) {
            offset += lines[i].length() + 1; // + '\n'
        }
        return Math.min(offset + column, Math.max(0, source.length() - 1));
    }

    /**
     * Reads the resource at the given URI as a string (Swing uses
     * {@code IOUtil.readFrom}, {@code IssueDialog.java:693}).
     */
    private static String readFrom(URI uri) throws IOException {
        try (var in = uri.toURL().openStream()) {
            return new String(in.readAllBytes(), java.nio.charset.StandardCharsets.UTF_8);
        }
    }

    /** @return the underlying JavaFX dialog (for owners/tests) */
    public Dialog<Void> getDialog() {
        return dialog;
    }

    /**
     * @return the most recently created dialog, if any — a self-test hook: the seam self test
     *         asserts that the {@code reportException} callback actually opened an
     *         {@link IssueDialogF} (the dialog itself cannot be enumerated from the stage)
     */
    public static Optional<IssueDialogF> getLastDialog() {
        return Optional.ofNullable(lastDialog);
    }

    /** @return {@code true} while the dialog is shown (self-test hook) */
    public boolean isVisible() {
        return dialog.isShowing();
    }

    /** @return the issues shown by this dialog (self-test hook) */
    public List<IssueEntry> getIssues() {
        return java.util.Collections.unmodifiableList(issues);
    }

    /** Forwards to the underlying dialog (this class wraps a {@link Dialog}). */
    public void showAndWait() {
        dialog.showAndWait();
    }
}
