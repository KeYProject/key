/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.sourceview;

import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collection;
import java.util.Objects;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.scene.text.Font;

import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.gui.fx.configuration.ConfigF;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofJavaSourceCollection;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;

import org.key_project.util.java.IOUtil;
import org.key_project.util.javafx.FxUtil;

import org.fxmisc.richtext.Caret;
import org.fxmisc.richtext.LineNumberFactory;
import org.fxmisc.richtext.StyleClassedTextArea;
import org.fxmisc.richtext.model.StyleSpans;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * First JavaFX version of the source view, the counter-part of
 * {@code de.uka.ilkd.key.gui.sourceview.SourceView} (a tabbed pane of styled, read-only
 * {@code JTextPane}s) in the module {@code key.ui}.
 * <p>
 * <b>Milestone M2, first read-only version.</b> The view is a {@link StyleClassedTextArea}
 * (RichTextFX) showing the source file(s) of the selected proof:
 * <ul>
 * <li>the relevant files are obtained exactly like in the Swing view: the proof's
 * {@link ProofJavaSourceCollection} is populated from the {@link OriginTermLabel.FileOrigin}s of
 * the root sequent (port of {@code SourceView.ensureProofJavaSourceCollectionExists}) and read
 * through the proof's {@link FileRepo} ({@code proof.getInitConfig().getFileRepo()});</li>
 * <li>if the proof has no Java source at all (e.g. pure {@code .key} problem files like the
 * Agatha example, whose terms carry no origin labels), the view falls back to the file given via
 * {@link #setFallbackSourceFile(Path)} (typically the loaded {@code .key} file) so that the user
 * still sees the problem specification; if even that is unavailable, a dimmed
 * {@code "No source loaded"} placeholder is shown;</li>
 * <li>minimal syntax highlighting (keywords, comments, strings, annotations, JML keywords inside
 * annotations) is computed by {@link SourceHighlighter} on a background thread and applied in one
 * {@code setStyleSpans} call on the FX thread;</li>
 * <li>line numbers come from {@link LineNumberFactory}, the view is not editable and uses the
 * monospaced font from {@link ConfigF#DEFAULT}.</li>
 * </ul>
 * <p>
 * Deliberately deferred to later milestones (the Swing view does much more): the tab-per-file UI,
 * the proof-node &harr; source-line mapping (symbolic execution highlighting derived from the
 * {@code PositionInfo} of the active statements), tooltips, the click-to-jump navigation into the
 * proof tree, and re-highlighting on {@code selectedNodeChanged}.
 */
public class SourceViewF extends StyleClassedTextArea {

    private static final Logger LOGGER = LoggerFactory.getLogger(SourceViewF.class);

    /**
     * Placeholder for an empty view (as in the Swing source view's status bar).
     */
    public static final String NO_SOURCE = "No source loaded";

    /**
     * Placeholder for a file that could not be read (as in the Swing source view's tabs).
     */
    private static final String SOURCE_COULD_NOT_BE_LOADED = "[SOURCE COULD NOT BE LOADED]";

    /**
     * Indicates how many spaces are inserted instead of one tab (used in the Swing source view).
     */
    private static final int TAB_SIZE = 4;

    private KeYSelectionModel selectionModel;
    private Proof proof;
    /** identity of the currently shown source (URI or fallback path), used by the reload guard */
    private String shownKey = "";
    /** guards against applying the result of a stale background load */
    private int generation;
    /** the last highlighting result applied to the document (volatile: read by the self-test) */
    private volatile SourceHighlighter.Result applied = SourceHighlighter.Result.EMPTY;
    /**
     * optional fallback file (e.g. the loaded .key file) shown when the proof has no Java source
     */
    private volatile Path fallbackSourceFile;
    /** invoked on the FX thread after real source content (not a placeholder) was applied */
    private Runnable onContentLoaded = () -> {
    };

    private final StringProperty headerText =
        new SimpleStringProperty(this, "headerText", NO_SOURCE);

    private final KeYSelectionListener selectionListener = new KeYSelectionListener() {
        @Override
        public void selectedNodeChanged(KeYSelectionEvent<Node> event) {
            // deferred: the Swing view updates the symbolic execution highlights here
        }

        @Override
        public void selectedProofChanged(KeYSelectionEvent<Proof> event) {
            reload(event.getSource().getSelectedProof());
        }
    };

    /**
     * Creates an empty source view showing the "No source loaded" placeholder.
     */
    public SourceViewF() {
        getStyleClass().add("source-view");
        setEditable(false);
        setWrapText(false);
        getCaretSelectionBind().setShowCaret(Caret.CaretVisibility.OFF);
        paragraphGraphicFactoryProperty().set(LineNumberFactory.get(this));
        applyMonoFont();
        showPlaceholder(NO_SOURCE);
    }

    /**
     * Applies the monospaced font configured by {@link ConfigF} to the view. The font is set as
     * an inline style on the area node (the only way to feed a runtime {@link Font} into
     * RichTextFX's style-classed text); the segment colors themselves come from the theme
     * stylesheets via the {@code source-*} style classes.
     */
    private void applyMonoFont() {
        Font font = ConfigF.DEFAULT.monoFont();
        setStyle("-fx-font-family: \"" + font.getFamily() + "\"; -fx-font-size: "
            + font.getSize() + "px;");
        LOGGER.debug("Source view font: family={}, size={}", font.getFamily(), font.getSize());
    }

    /**
     * Registers this view as a selection listener on the given model and shows the source of the
     * currently selected proof, if any (same {@code attach} pattern as the other M2 views).
     *
     * @param model the selection model to observe
     */
    public void attach(KeYSelectionModel model) {
        Objects.requireNonNull(model);
        if (selectionModel == model) {
            return;
        }
        if (selectionModel != null) {
            selectionModel.removeKeYSelectionListener(selectionListener);
        }
        selectionModel = model;
        model.addKeYSelectionListenerChecked(selectionListener);
        reload(model.getSelectedProof());
    }

    /**
     * Sets the fallback file shown when the selected proof carries no Java source (pure
     * {@code .key} problem files have no {@link OriginTermLabel.FileOrigin}s in their sequent, so
     * the {@link ProofJavaSourceCollection} stays empty). The standalone drivers pass the loaded
     * problem file here; {@code MainWindowF} may keep this unset and always show the placeholder.
     *
     * @param file the file to fall back to, or {@code null} to disable the fallback
     */
    public void setFallbackSourceFile(Path file) {
        fallbackSourceFile = file;
    }

    /**
     * Text describing the currently shown source (file name and mode); bind a header label to
     * it. Updated by the view whenever new content is applied.
     *
     * @return the header text property
     */
    public StringProperty headerTextProperty() {
        return headerText;
    }

    /**
     * Registers a hook that is invoked on the FX thread after real source content (not the
     * placeholder) has been applied. Used by the drivers to run the self-test after display.
     *
     * @param hook the hook to run, may be {@code null} to clear it
     */
    public void setOnContentLoaded(Runnable hook) {
        onContentLoaded = hook != null ? hook : () -> {
        };
    }

    /**
     * Reloads the view for the given proof. Skips the reload if the same proof would show the
     * same file again. The source file is determined on the FX thread (this registers the
     * {@link ProofJavaSourceCollection} like the Swing view does), while reading the file and
     * computing the highlighting run on a background thread.
     *
     * @param newProof the proof whose source should be shown, may be {@code null}
     */
    private void reload(Proof newProof) {
        if (!FxUtil.isFxThread()) {
            FxUtil.runLater(() -> reload(newProof));
            return;
        }
        URI uri = newProof != null ? ensureAndPickSourceFile(newProof) : null;
        Path fallback = uri == null && newProof != null ? fallbackSourceFile : null;
        String key = uri != null ? uri.toString()
                : fallback != null ? fallback.toString() : "";
        if (newProof == proof && key.equals(shownKey)) {
            return; // guard: same proof, same file
        }
        proof = newProof;
        shownKey = key;
        final int gen = ++generation;
        if (newProof == null) {
            showPlaceholder(NO_SOURCE);
            return;
        }
        Thread loader = new Thread(() -> {
            Loaded loaded = readAndHighlight(gen, newProof, uri, fallback);
            FxUtil.runLater(() -> apply(loaded));
        }, "fx-source-view-loader");
        loader.setDaemon(true);
        loader.start();
    }

    /**
     * Ports {@code SourceView.ensureProofJavaSourceCollectionExists} of the Swing view: makes
     * sure the proof has a {@link ProofJavaSourceCollection} and populates it from the
     * {@link OriginTermLabel.FileOrigin}s found on the terms of the root sequent. Then returns
     * one of the relevant files (the first; the Swing view opens all of them in tabs, which is
     * deferred here).
     *
     * @param proof the proof to inspect, not {@code null}
     * @return a relevant source file URI, or {@code null} if the proof has none
     */
    private static URI ensureAndPickSourceFile(Proof proof) {
        if (proof.lookup(ProofJavaSourceCollection.class) == null) {
            final var sources = new ProofJavaSourceCollection();
            proof.register(sources, ProofJavaSourceCollection.class);
            proof.root().sequent().forEach(formula -> {
                OriginTermLabel originLabel =
                    (OriginTermLabel) ((JTerm) formula.formula()).getLabel(OriginTermLabel.NAME);
                if (originLabel != null) {
                    if (originLabel.getOrigin() instanceof OriginTermLabel.FileOrigin fileOrigin) {
                        fileOrigin.getFileName().ifPresent(sources::addRelevantFile);
                    }

                    originLabel.getSubtermOrigins().stream()
                            .filter(o -> o instanceof OriginTermLabel.FileOrigin)
                            .map(o -> (OriginTermLabel.FileOrigin) o)
                            .forEach(o -> o.getFileName().ifPresent(sources::addRelevantFile));
                }
            });
        }
        ProofJavaSourceCollection sources = proof.lookup(ProofJavaSourceCollection.class);
        return sources != null && !sources.getRelevantFiles().isEmpty()
                ? sources.getRelevantFiles().iterator().next()
                : null;
    }

    /**
     * Reads the source text and computes the highlighting off the FX-critical path.
     * <p>
     * Tries, in order: the relevant file of the proof's source collection (via the proof's
     * {@link FileRepo}, like the Swing view), then the fallback file ({@code .key} mode), then
     * the "No source loaded" placeholder.
     *
     * @param gen the reload generation this load belongs to
     * @param proof the proof (source of the {@link FileRepo}), not {@code null}
     * @param uri the relevant source file, may be {@code null}
     * @param fallback the fallback file, may be {@code null}
     * @return the loaded content together with the highlighting result
     */
    private static Loaded readAndHighlight(int gen, Proof proof, URI uri, Path fallback) {
        if (uri != null) {
            Loaded loaded = readRepoFile(gen, proof, uri);
            if (loaded != null) {
                return loaded;
            }
        }
        if (fallback != null) {
            Loaded loaded = readLocalFile(gen, fallback);
            if (loaded != null) {
                return loaded;
            }
        }
        return Loaded.placeholder(gen, NO_SOURCE);
    }

    /**
     * Reads a relevant file of the proof through the proof's {@link FileRepo} (the Swing view's
     * {@code addFile} path: {@code repo.getInputStream(fileURI.toURL())}).
     *
     * @return the loaded content, or {@code null} if the file could not be read
     */
    private static Loaded readRepoFile(int gen, Proof proof, URI uri) {
        try {
            FileRepo repo = proof.getInitConfig().getFileRepo();
            try (InputStream is = repo.getInputStream(uri.toURL())) {
                if (is == null) {
                    LOGGER.debug("FileRepo has no stream for {}", uri);
                    return null;
                }
                return build(gen, simpleFileName(uri), IOUtil.readFrom(is));
            }
        } catch (IOException e) {
            LOGGER.debug("Could not read source file {}", uri, e);
            return null;
        }
    }

    /**
     * Reads the fallback file directly from disk ({@code .key} mode: the proof has no Java
     * source, so the problem specification is shown instead).
     *
     * @return the loaded content, or {@code null} if the file could not be read
     */
    private static Loaded readLocalFile(int gen, Path file) {
        try (InputStream is = Files.newInputStream(file)) {
            String header = file.getFileName()
                + " (no Java source in proof — showing problem file)";
            return build(gen, header, IOUtil.readFrom(is));
        } catch (IOException e) {
            LOGGER.debug("Could not read fallback source file {}", file, e);
            return null;
        }
    }

    /**
     * Computes the highlighting for the given text (replacing tabs like the Swing view).
     *
     * @return the loaded content, or the "could not be loaded" placeholder on I/O errors
     */
    private static Loaded build(int gen, String header, String text) {
        String cleaned = replaceTabs(text);
        if (cleaned.isBlank()) {
            return Loaded.placeholder(gen, SOURCE_COULD_NOT_BE_LOADED);
        }
        SourceHighlighter.Result result = SourceHighlighter.highlight(cleaned);
        int lines = cleaned.split("\n", -1).length;
        return new Loaded(gen, header + " · " + lines + " lines", cleaned, result.spans(), result,
            true);
    }

    /**
     * Applies a finished background load to the document (FX thread only).
     */
    private void apply(Loaded loaded) {
        FxUtil.assertFxThread();
        if (loaded.generation() != generation) {
            LOGGER.debug("Ignoring stale source load (generation {})", loaded.generation());
            return;
        }
        clear();
        if (!loaded.text().isEmpty()) {
            appendText(loaded.text());
            if (loaded.spans() != null) {
                setStyleSpans(0, loaded.spans());
            }
            // appendText parks the caret (and the scroll) at the end; the Swing view shows the
            // top of the file
            showParagraphAtTop(0);
        }
        applied = loaded.result();
        headerText.set(loaded.header());
        if (loaded.success() && !loaded.text().isEmpty()) {
            onContentLoaded.run();
        }
    }

    /**
     * Shows a dimmed placeholder text (no proof, or nothing could be loaded).
     */
    private void showPlaceholder(String text) {
        FxUtil.assertFxThread();
        clear();
        applied = SourceHighlighter.Result.EMPTY;
        headerText.set(NO_SOURCE);
        if (!text.isEmpty()) {
            appendText(text);
            setStyleSpans(0, SourceHighlighter.placeholderSpans(text));
            showParagraphAtTop(0);
        }
    }

    /**
     * Development self-test (M2): verifies that the view shows non-empty source text and that
     * the highlighting produced highlighted spans (counted per category while tokenizing; the
     * categories themselves may legitimately be zero, e.g. no string literals in a {@code .key}
     * file). Also checks that the applied text length matches the document length.
     *
     * @return a one-line report ending in {@code PASS} or {@code FAIL}
     */
    public String verifySourceView() {
        SourceHighlighter.Result result = applied;
        if (result == null || result.length() <= 0 || getLength() <= 0) {
            return "len=" + (result == null ? 0 : result.length()) + " textLen=" + getLength()
                + " total=0 FAIL (no source loaded)";
        }
        boolean pass = result.length() == getLength() && result.total() > 0;
        return "len=" + result.length() + " textLen=" + getLength() + " keywords="
            + result.keywords() + " comments=" + result.comments() + " strings=" + result.strings()
            + " annotations=" + result.annotations() + " jmlKeywords=" + result.jmlKeywords()
            + " total=" + result.total() + " " + (pass ? "PASS" : "FAIL");
    }

    /**
     * Replaces each tab by {@link #TAB_SIZE} spaces (port of the Swing view's {@code replaceTabs}).
     */
    private static String replaceTabs(String s) {
        char[] replacement = new char[TAB_SIZE];
        Arrays.fill(replacement, ' ');
        return s.replace("\t", new String(replacement));
    }

    /**
     * @return the file name of the given URI (after the last '/'), like the Swing view's tab
     *         titles
     */
    private static String simpleFileName(URI uri) {
        String s = uri.toString();
        int index = s.lastIndexOf('/');
        return index < 0 ? s : s.substring(index + 1);
    }

    /**
     * One finished (background) load: text, highlighting spans and the header line for it.
     */
    private record Loaded(int generation, String header, String text,
            StyleSpans<Collection<String>> spans, SourceHighlighter.Result result,
            boolean success) {

        static Loaded placeholder(int generation, String text) {
            return new Loaded(generation, NO_SOURCE, text,
                text.isEmpty() ? null : SourceHighlighter.placeholderSpans(text),
                SourceHighlighter.Result.EMPTY, false);
        }
    }
}
