/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.proofdiff;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.scene.text.Font;
import javafx.stage.Stage;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.configuration.ConfigF;
import de.uka.ilkd.key.gui.fx.proofdiff.diff_match_patch.Diff;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Levensthein;

import org.key_project.util.javafx.FxUtil;

import org.fxmisc.richtext.Caret;
import org.fxmisc.richtext.StyleClassedTextArea;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * JavaFX version of the proof node diff window, counter-part of
 * {@code de.uka.ilkd.key.gui.proofdiff.ProofDiffFrame} in the module {@code key.ui}.
 * <p>
 * Proof-of-concept implementation of a textual sequent comparison (as the Swing javadoc puts
 * it): the window lets the user display an in-place comparison of two sequents of the currently
 * selected proof. The comparison happens on the pretty-printed text only, using the bundled
 * {@link diff_match_patch} library. Port notes:
 * <ul>
 * <li>the Swing {@code JEditorPane} with HTML content ({@code <pre>} plus
 * {@code <span style='background-color: ...'>} markup) becomes a read-only
 * {@link StyleClassedTextArea} (RichTextFX, the presentation of the source view): the diff is
 * rendered as plain text and the deleted/inserted parts are highlighted via the style classes
 * {@link #CLASS_DELETE} (red background) and {@link #CLASS_INSERT} (green background), computed
 * by {@link #render(LinkedList)} — the JavaFX counterpart of the Swing HTML loop;</li>
 * <li>the node fields, buttons, tooltips and the help text follow the Swing original one to one
 * (including the default button "Show Diff" and the always-enabled menu action); error popups
 * ({@code JOptionPane}) become {@link Alert}s;</li>
 * <li>like the Swing frame, the diff is computed synchronously on the UI thread (the Swing
 * original runs on the EDT) — sequent texts are small and {@code Diff_Timeout} is set to 0 as in
 * the original.</li>
 * </ul>
 */
public class ProofDiffFrameF extends Stage {

    private static final Logger LOGGER = LoggerFactory.getLogger(ProofDiffFrameF.class);

    /** Window size of the Swing original ({@code setSize(700, 600)}). */
    private static final double WIDTH = 700;
    private static final double HEIGHT = 600;

    /** Style class of highlighted text present only in the parent sequent (red background). */
    public static final String CLASS_DELETE = "diff-delete";

    /** Style class of highlighted text added in the child sequent (green background). */
    public static final String CLASS_INSERT = "diff-insert";

    /** Style class of the bold headings in the help text. */
    public static final String CLASS_HELP_HEADING = "diff-help-heading";

    /**
     * The main window, the source of the selected proof (Swing {@code ProofDiffFrame.mainWindow}).
     */
    private final MainWindowF mainWindow;

    /**
     * The text area displaying the diff'ed text (Swing {@code textArea}: a read-only HTML
     * {@code JEditorPane} with the sequent font).
     */
    private final StyleClassedTextArea textArea = new StyleClassedTextArea();

    /** The text field holding the lower comparison number (Swing {@code from}). */
    private final TextField from = new TextField();

    /** The text field holding the upper comparison number (Swing {@code to}). */
    private final TextField to = new TextField();

    /**
     * Instantiates a new proof-diff window (Swing ctor: {@code ProofDiffFrame(MainWindow)}).
     *
     * @param mainWindow the main window of the system
     */
    public ProofDiffFrameF(MainWindowF mainWindow) {
        this.mainWindow = mainWindow;
        setTitle("Visual difference between two sequents");
        if (mainWindow.getStage() != null) {
            initOwner(mainWindow.getStage());
        }
        Scene scene = new Scene(guiInit(), WIDTH, HEIGHT);
        ThemeManager.getInstance().manage(scene);
        setScene(scene);
    }

    /**
     * Opens the window centered on the main window (Swing
     * {@code pdf.setLocationRelativeTo(mainWindow)}).
     */
    public void showCenteredOnOwner() {
        Stage owner = mainWindow.getStage();
        if (owner != null && owner.isShowing()) {
            setX(owner.getX() + (owner.getWidth() - WIDTH) / 2);
            setY(owner.getY() + (owner.getHeight() - HEIGHT) / 2);
        }
        show();
        textArea.requestFocus();
    }

    /**
     * Initializes the user interface (Swing {@code guiInit}: the diff area in the center, the
     * node fields and buttons at the bottom).
     *
     * @return the root node of the window
     */
    private BorderPane guiInit() {
        BorderPane root = new BorderPane();
        textArea.getStyleClass().add("proof-diff-area");
        textArea.setEditable(false);
        textArea.setWrapText(false);
        textArea.getCaretSelectionBind().setShowCaret(Caret.CaretVisibility.OFF);
        applyMonoFont();
        showHelp();
        root.setCenter(textArea);

        HBox bottom = new HBox(8);
        bottom.getStyleClass().add("proof-diff-controls");
        bottom.setAlignment(javafx.geometry.Pos.CENTER_RIGHT);

        from.setPrefColumnCount(5);
        from.setTooltip(
            new Tooltip("Set the parent node to compare. May be empty for the direct predecessor"));
        to.setPrefColumnCount(5);
        to.setTooltip(new Tooltip("Set the child node to compare. Must not be empty"));

        Button go = new Button("Show Diff");
        go.setTooltip(new Tooltip("Show difference between the two nodes specified here."));
        go.setDefaultButton(true);
        go.setOnAction(e -> showDiff());

        Button last = new Button("Show Selected Node");
        last.setTooltip(new Tooltip(
            "Show difference introduced by the rule application leading to the selected node"));
        last.setOnAction(e -> {
            setSelectedNode();
            showDiff();
        });

        Button close = new Button("Close");
        close.setOnAction(e -> hide());

        bottom.getChildren()
                .addAll(new Label("Parent node:"), from, new Label("Proof node:"), to, go, last,
                    close);
        root.setBottom(bottom);
        return root;
    }

    /**
     * Applies the monospaced sequent font configured by {@link ConfigF} to the view (the Swing
     * original sets {@code UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW)}); the font is set as
     * an inline style on the area node, the same way the source view does it.
     */
    private void applyMonoFont() {
        Font font = ConfigF.DEFAULT.monoFont();
        textArea.setStyle("-fx-font-family: \"" + font.getFamily() + "\"; -fx-font-size: "
            + font.getSize() + "px;");
    }

    /**
     * Sets the to field to the selected node. Clears the from field (Swing
     * {@code setSelectedNode}).
     */
    private void setSelectedNode() {
        try {
            Node node = mainWindow.getMediator().getSelectedNode();
            if (node == null) {
                throw new IllegalArgumentException("There is no selected proof node or no proof!");
            }

            from.setText("");
            to.setText(Integer.toString(node.serialNr()));
        } catch (IllegalArgumentException e) {
            showError(e.getMessage());
        }
    }

    /**
     * Initiate a diff calculation and set the content of the text area (Swing {@code showDiff}).
     * <p>
     * It uses the result of {@link diff_match_patch#diff_main(String, String, boolean)} and the
     * styled-range rendering of {@link #render(LinkedList)} to show the text.
     */
    private void showDiff() {
        String sFrom;
        String sTo;

        try {
            int toNo;
            String toText = to.getText();
            if (toText.isEmpty()) {
                throw new IllegalArgumentException(
                    "At least the second proof node must be specified");
            } else {
                toNo = Integer.parseInt(to.getText());
                sTo = getProofNodeText(toNo);
            }

            String fromText = from.getText();
            if (fromText.isEmpty()) {
                sFrom = getProofNodeText(getParent(toNo));
            } else {
                int fromNo = Integer.parseInt(fromText);
                sFrom = getProofNodeText(fromNo);
            }
        } catch (NumberFormatException e) {
            showError("This is not a number: " + e.getMessage());
            return;
        } catch (IllegalArgumentException e) {
            showError(e.getMessage());
            return;
        }

        diff_match_patch differ = new diff_match_patch();
        differ.Diff_Timeout = 0.0f;
        LinkedList<Diff> diffs = differ.diff_main(sFrom, sTo, false);

        Rendered rendered = render(diffs);
        display(rendered.text(), rendered.ranges());
        LOGGER.info(
            "Proof diff of node '{}' vs '{}': {} chars, {} highlighted range(s)",
            from.getText(), to.getText(), rendered.text().length(), rendered.ranges().size());
    }

    /**
     * One highlighted range of the displayed text — the JavaFX counterpart of the Swing
     * {@code <span style='background-color: ...'>} markup.
     */
    record StyledRange(int start, int end, String styleClass) {
    }

    /**
     * A rendered diff: the concatenated text (all diff chunks, like the Swing {@code <pre>}
     * content) plus the ranges to highlight.
     */
    record Rendered(String text, List<StyledRange> ranges) {
    }

    /**
     * Ports the HTML markup loop of the Swing frame: {@code EQUAL} stays plain, {@code DELETE}
     * gets the red background and {@code INSERT} the green one — whitespace-only edits stay
     * unmarked, exactly as in the Swing original.
     *
     * @param diffs the diff chunks produced by {@code diff_main}
     * @return the rendered text and the highlighted ranges into it
     */
    static Rendered render(LinkedList<Diff> diffs) {
        StringBuilder sb = new StringBuilder();
        List<StyledRange> ranges = new ArrayList<>();
        int pos = 0;
        for (Diff diff : diffs) {
            int start = pos;
            sb.append(diff.text);
            pos = sb.length();
            switch (diff.operation) {
                case EQUAL -> {
                }
                case DELETE -> {
                    if (!onlySpaces(diff.text)) {
                        ranges.add(new StyledRange(start, pos, CLASS_DELETE));
                    }
                }
                case INSERT -> {
                    if (!onlySpaces(diff.text)) {
                        ranges.add(new StyledRange(start, pos, CLASS_INSERT));
                    }
                }
            }
        }
        return new Rendered(sb.toString(), ranges);
    }

    private static boolean onlySpaces(CharSequence text) {
        for (int i = 0; i < text.length(); i++) {
            if (!Character.isWhitespace(text.charAt(i))) {
                return false;
            }
        }
        return true;
    }

    /**
     * Replaces the content of the diff area (FX thread only): the plain text plus the
     * highlighted ranges.
     */
    private void display(String text, List<StyledRange> ranges) {
        FxUtil.assertFxThread();
        textArea.clear();
        if (!text.isEmpty()) {
            textArea.appendText(text);
            for (StyledRange range : ranges) {
                textArea.setStyleClass(range.start(), range.end(), range.styleClass());
            }
            // the Swing view shows the beginning of the diff after a update
            textArea.moveTo(0);
            textArea.showParagraphAtTop(0);
        }
    }

    private int getParent(int no) {
        Proof proof = mainWindow.getMediator().getSelectedProof();
        if (proof == null) {
            throw new IllegalArgumentException("There is no open proof!");
        }

        Node node = findNode(proof.root(), no);
        if (node == null) {
            throw new IllegalArgumentException(no + " is not a node in the proof");
        }

        Node parent = node.parent();
        if (parent == null) {
            throw new IllegalArgumentException(no + " has no parent node");
        }

        return parent.serialNr();
    }

    /**
     * Gets the pretty printed node text for a node (Swing {@code getProofNodeText}: the printed
     * sequent of the node with the given serial number).
     *
     * @param nodeNumber the number of the node to search
     * @return the proof node text
     * @throws IllegalArgumentException if the number is bad or there is no proof.
     */
    private String getProofNodeText(int nodeNumber) {
        Proof proof = mainWindow.getMediator().getSelectedProof();

        if (proof == null) {
            throw new IllegalArgumentException("There is no open proof!");
        }

        Node node = findNode(proof.root(), nodeNumber);

        if (node == null) {
            throw new IllegalArgumentException(nodeNumber + " does not denote a valid node");
        }

        return LogicPrinter.quickPrintSequent(node.sequent(), proof.getServices());
    }

    // This must have been implemented already, somewhere (Swing comment kept).
    private Node findNode(Node node, int number) {
        if (node.serialNr() == number) {
            return node;
        }

        while ((node.serialNr() != number) && (node.childrenCount() == 1)) {
            node = node.child(0);
        }

        if (node.serialNr() == number) {
            return node;
        }

        Iterator<Node> it = node.childrenIterator();
        while (it.hasNext()) {
            Node n = it.next();
            if (n.serialNr() <= number) {
                Node result = findNode(n, number);
                if (result != null) {
                    return result;
                }
            }
        }

        return null;
    }

    /**
     * The help text of the Swing frame ({@code getHelpText()}, its HTML converted to the styled
     * text presentation; the red/green example words keep their background colors).
     */
    private void showHelp() {
        List<HelpSegment> segments = List.of(
            new HelpSegment("Visual diff between sequents of Proof Nodes\n\n", CLASS_HELP_HEADING),
            new HelpSegment(
                "This window can be used to select one or two sequents of an "
                    + "ongoing or closed proof. All actions refer to the currently selected proof.\n\n",
                null),
            new HelpSegment(
                "The text area shows the in-place diff between two pretty printed "
                    + "sequents. Parts in ",
                null),
            new HelpSegment("red", CLASS_DELETE),
            new HelpSegment(" are only present in the parent sequent and parts in ", null),
            new HelpSegment("green", CLASS_INSERT),
            new HelpSegment(" are added in the second proof node.\n\n", null),
            new HelpSegment("One node mode\n", CLASS_HELP_HEADING),
            new HelpSegment(
                "If you keep the left field (parent node) empty, the difference between the "
                    + "proof node and its direct predecessor is displayed in the text area.\n\n",
                null),
            new HelpSegment("Two node mode\n", CLASS_HELP_HEADING),
            new HelpSegment(
                "If you specify two nodes, the difference between the declared sequents "
                    + "are displayed.\n\n",
                null),
            new HelpSegment("'Show selected node'\n", CLASS_HELP_HEADING),
            new HelpSegment(
                "Use this button to use the currently selected proof node of the proof "
                    + "component as displayed proof node.",
                null));
        StringBuilder sb = new StringBuilder();
        List<StyledRange> ranges = new ArrayList<>();
        for (HelpSegment segment : segments) {
            int start = sb.length();
            sb.append(segment.text());
            if (segment.styleClass() != null) {
                ranges.add(new StyledRange(start, sb.length(), segment.styleClass()));
            }
        }
        display(sb.toString(), ranges);
    }

    /**
     * One styled run of the help text ({@code null} style class means plain text).
     */
    private record HelpSegment(String text, String styleClass) {
    }

    /**
     * Shows the message of a rejected diff in an error dialog (the Swing original opens a
     * {@code JOptionPane} error message dialog).
     *
     * @param message the error message, not {@code null}
     */
    private void showError(String message) {
        LOGGER.info("Proof diff rejected: {}", message);
        Alert alert = new Alert(Alert.AlertType.ERROR);
        alert.initOwner(this);
        alert.setTitle("Error");
        alert.setHeaderText("Error");
        alert.setContentText(message);
        alert.showAndWait();
    }

    /**
     * Development self-test ({@code key.fx.verify.proofdiff}): ports the assertions of the Swing
     * unit test {@code de.uka.ilkd.key.gui.proofdiff.ProofDifferenceTest} (edit distance and
     * sequent formula pairing) and adds sanity checks on the bundled {@link diff_match_patch} and
     * the styled-range rendering used by the window (identical texts produce no highlight,
     * whitespace-only edits are not highlighted). Pure logic, no UI — runs on any thread.
     *
     * @return a one-line report ending in {@code PASS} or {@code FAIL}
     */
    public static String verifyDiffLogic() {
        List<String> failures = new ArrayList<>();

        // edit distance (Swing ProofDifferenceTest.testLevensthein)
        if (Levensthein.calculate("abc", "abc") != 0) {
            failures.add("levensthein(abc,abc)!=0");
        }
        if (Levensthein.calculate("!p", "p") != 1) {
            failures.add("levensthein(!p,p)!=1");
        }
        if (Levensthein.calculate("f(x)", "f(g(x))") != 3) {
            failures.add("levensthein(f(x),f(g(x)))!=3");
        }
        if (Levensthein.calculate("f(x)", "") != 4) {
            failures.add("levensthein(f(x),\")!=4");
        }

        // formula pairing (Swing ProofDifferenceTest.testPairs1)
        expectPairs(failures, List.of("a", "b", "c"), List.of("a", "b", "c"),
            "[(a, a), (b, b), (c, c)]");
        expectPairs(failures, List.of("d", "b", "c"), List.of("a", "b", "c"),
            "[(b, b), (c, c), (d, a)]");
        expectPairs(failures, List.of("p->q", "!q", "p"), List.of("p", "p->!q", "!p"),
            "[(p, p), (p->q, p->!q), (!q, !p)]");

        // diff_match_patch: identical texts produce a single plain chunk (the "empty diff" case)
        Rendered same = dmp("Hello world", "Hello world");
        if (!same.text().equals("Hello world") || !same.ranges().isEmpty()) {
            failures.add("identical texts: text=" + same.text() + " ranges=" + same.ranges());
        }

        // a modification: the highlighted ranges must carry exactly the DELETE/INSERT chunks the
        // library produced (dmp may split words around common characters, e.g. "world" ->
        // "there" is DEL"wo" INS"the" EQ"r" DEL"ld" INS"e"); the library's own reconstruction
        // (diff_text1/diff_text2) proves the diff itself is intact
        diff_match_patch differ = new diff_match_patch();
        differ.Diff_Timeout = 0.0f;
        LinkedList<Diff> diffs = differ.diff_main("Hello world", "Hello there", false);
        Rendered mod = render(diffs);
        if (!differ.diff_text1(diffs).equals("Hello world")
                || !differ.diff_text2(diffs).equals("Hello there")) {
            failures.add("dmp reconstruction: t1=" + differ.diff_text1(diffs) + " t2="
                + differ.diff_text2(diffs));
        }
        if (!String.join("", highlighted(mod, CLASS_DELETE))
                .equals(chunks(diffs, diff_match_patch.Operation.DELETE))
                || !String.join("", highlighted(mod, CLASS_INSERT))
                        .equals(chunks(diffs, diff_match_patch.Operation.INSERT))) {
            failures.add("modification: delete=" + highlighted(mod, CLASS_DELETE) + " insert="
                + highlighted(mod, CLASS_INSERT));
        }

        // whitespace-only edits are not highlighted (Swing onlySpaces rule)
        Rendered ws = dmp("a b", "ab");
        if (!ws.ranges().isEmpty()) {
            failures.add("whitespace-only edit highlighted: " + ws.ranges());
        }

        return "levensthein=4 pairs=3 patch=3 " + (failures.isEmpty() ? "PASS"
                : "FAIL: "
                    + String.join("; ", failures));
    }

    /**
     * Runs the diff through the window's own pipeline ({@link diff_match_patch} with
     * {@code Diff_Timeout = 0} + {@link #render}).
     */
    private static Rendered dmp(String left, String right) {
        diff_match_patch differ = new diff_match_patch();
        differ.Diff_Timeout = 0.0f;
        return render(differ.diff_main(left, right, false));
    }

    /**
     * @return the substrings of the rendered text highlighted with the given style class
     */
    private static List<String> highlighted(Rendered rendered, String styleClass) {
        return rendered.ranges().stream()
                .filter(range -> range.styleClass().equals(styleClass))
                .map(range -> rendered.text().substring(range.start(), range.end()))
                .toList();
    }

    /**
     * @return the concatenation of the texts of all chunks with the given operation
     */
    private static String chunks(List<Diff> diffs, diff_match_patch.Operation operation) {
        StringBuilder sb = new StringBuilder();
        for (Diff diff : diffs) {
            if (diff.operation == operation) {
                sb.append(diff.text);
            }
        }
        return sb.toString();
    }

    /**
     * Compares the pairing result against the expectation of the Swing test.
     */
    private static void expectPairs(List<String> failures, List<String> left, List<String> right,
            String expected) {
        List<ProofDifference.Matching> pairs =
            ProofDifference.findPairs(new ArrayList<>(left), new ArrayList<>(right));
        if (!expected.equals(pairs.toString())) {
            failures.add("findPairs(" + left + ", " + right + ") = " + pairs);
        }
    }
}
