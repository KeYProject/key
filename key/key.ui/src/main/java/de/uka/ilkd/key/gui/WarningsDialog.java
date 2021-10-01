package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.sourceview.JavaDocument;
import de.uka.ilkd.key.gui.sourceview.TextLineNumber;
import de.uka.ilkd.key.gui.utilities.BracketMatchingTextArea;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.util.Debug;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.IOUtil;

import javax.annotation.Nullable;
import javax.swing.*;
import javax.swing.border.Border;
import javax.swing.border.EmptyBorder;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import javax.swing.text.SimpleAttributeSet;
import java.awt.*;
import java.awt.event.KeyEvent;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.URI;
import java.util.List;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A dialog for showing multiple warnings with a preview window.
 * <p>
 * This dialog has support to:
 * <ul>
 *     <li>hide listed warnings for the current session</li>
 *     <li>show the warning in a little preview window (with syntax highlighting)</li>
 *     <li>if an URL is in the description, it is possible to open this web page</li>
 *     <li>if a file name is associated with the warning, the user can open its editor</li>
 * </ul>
 *
 * @author Alexander Weigl
 * @version 1 (6/8/21)
 */
public class WarningsDialog extends JDialog {
    private static final Set<PositionedString> ignoredWarnings = new HashSet<>();

    private final List<PositionedString> warnings;
    private final Map<String, String> fileContentsCache = new HashMap<>();
    private final JTextPane txtSource = new JTextPane();
    private final JList<PositionedString> listWarnings;
    private final JButton btnFurtherInformation = new JButton("Further Information", IconFactory.help(16));
    private final JButton btnOpenFile = new JButton("Edit File", IconFactory.editFile(16));

    @Nullable
    private String urlFurtherInformation;

    public WarningsDialog(Frame owner, Set<PositionedString> warnings) {
        super(owner, SLEnvInput.getLanguage() + " warning(s)", true);

        setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
        this.warnings = new ArrayList<>(warnings);
        this.warnings.sort(Comparator.comparing(o -> o.fileName));

        setLayout(new BorderLayout());
        JSplitPane splitCenter = new JSplitPane(JSplitPane.VERTICAL_SPLIT, false);
        add(splitCenter, BorderLayout.CENTER);

        //top label
        final String head = String.format(
                "The following non-fatal problems occurred when translating your %s specifications:",
                SLEnvInput.getLanguage());

        JLabel label = new JLabel(head);
        label.setBorder(BorderFactory.createEmptyBorder(5, 5, 0, 5));
        add(label, BorderLayout.NORTH);

        listWarnings = new JList<>(this.warnings.toArray(new PositionedString[0]));
        listWarnings.addListSelectionListener(e -> updatePreview());
        listWarnings.addListSelectionListener(e -> updateFurtherInformation(listWarnings.getSelectedValue().text));
        listWarnings.addListSelectionListener(e ->
                btnOpenFile.setEnabled(listWarnings.getSelectedValue().hasFilename()));
        listWarnings.setCellRenderer(new PositionedStringRenderer());
        listWarnings.setBorder(BorderFactory.createLoweredBevelBorder());

        JScrollPane scrWarnings = new JScrollPane(listWarnings);
        scrWarnings.setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER);
        scrWarnings.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
        splitCenter.setLeftComponent(scrWarnings);

        JScrollPane scrPreview = new JScrollPane(txtSource);
        splitCenter.setRightComponent(scrPreview);

        TextLineNumber lineNumbers = new TextLineNumber(txtSource, 2);
        scrPreview.setRowHeaderView(lineNumbers);

        Font font = UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW);
        if (font == null) {
            // make sure a monospaced font is used
            font = new Font(Font.MONOSPACED, Font.PLAIN, 12);
        }
        txtSource.setFont(font);


        final JButton btnOk = new JButton("OK");
        btnOk.addActionListener(e -> accept());
        Dimension buttonDim = new Dimension(100, 27);
        btnOk.setPreferredSize(buttonDim);
        btnOk.setMinimumSize(buttonDim);


        Box pSouth = new Box(BoxLayout.Y_AXIS);
        JPanel pButtons = new JPanel(new FlowLayout(FlowLayout.CENTER));
        pButtons.add(btnOk);
        pButtons.add(btnFurtherInformation);
        pButtons.add(btnOpenFile);

        JCheckBox chkIgnoreWarnings = new JCheckBox("Ignore these warnings for the current session");
        pSouth.add(chkIgnoreWarnings);
        pSouth.add(pButtons);
        add(pSouth, BorderLayout.SOUTH);
        getRootPane().setDefaultButton(btnOk);

        btnFurtherInformation.addActionListener(e -> {
            if (urlFurtherInformation != null && !urlFurtherInformation.isEmpty()) {
                try {
                    Objects.requireNonNull(Desktop.getDesktop())
                            .browse(URI.create(urlFurtherInformation));
                } catch (IOException ex) {
                    JOptionPane.showMessageDialog(WarningsDialog.this, ex.getMessage());
                }
            }
        });

        btnOpenFile.addActionListener(e -> {
            final PositionedString selectedValue = listWarnings.getSelectedValue();
            if (selectedValue.hasFilename()) {
                try {
                    Objects.requireNonNull(Desktop.getDesktop())
                            .open(new File(selectedValue.fileName));
                } catch (IOException ex) {
                    JOptionPane.showMessageDialog(WarningsDialog.this, ex.getMessage());
                }
            }
        });

        btnOk.registerKeyboardAction(
                event -> {
                    if (event.getActionCommand().equals("ESC")) {
                        btnOk.doClick();
                    }
                },
                "ESC",
                KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
                JComponent.WHEN_IN_FOCUSED_WINDOW);

        setSize(700, 500);
        splitCenter.setDividerLocation(250);
        if (owner != null) {
            setLocationRelativeTo(owner);
        }
    }

    private void accept() {
        ignoredWarnings.addAll(warnings);
        setVisible(false);
    }

    public static void showIfNecessary(MainWindow mainWindow, ImmutableSet<PositionedString> warnings) {
        Set<PositionedString> warn = warnings.toSet();
        warn.removeAll(ignoredWarnings);
        WarningsDialog dialog = new WarningsDialog(mainWindow, warn);
        dialog.setVisible(true);
        dialog.dispose();
    }

    private void updatePreview() {
        try {
            PositionedString ps = listWarnings.getSelectedValue();
            String source = fileContentsCache.computeIfAbsent(ps.fileName, fn -> {
                try (InputStream stream = IOUtil.openStream(ps.fileName)) {
                    return IOUtil.readFrom(stream);
                } catch (IOException e) {
                    Debug.out("Unknown IOException!", e);
                    return "[SOURCE COULD NOT BE LOADED]\n" + e.getMessage();
                }
            });

            if (isJava(ps.fileName)) {
                showJavaSourceCode(ps, source);
            } else {
                txtSource.setText(source);
            }
            int offset = getOffsetFromLineColumn(source, ps.pos);
            txtSource.setCaretPosition(offset);
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    private void showJavaSourceCode(PositionedString ps, String source) {
        try {
            JavaDocument doc = new JavaDocument();
            txtSource.setDocument(doc);
            doc.insertString(0, source, new SimpleAttributeSet());
            DefaultHighlighter dh = new DefaultHighlighter();
            txtSource.setHighlighter(dh);
            addWarnings(dh, ps.fileName);
        } catch (BadLocationException e) {
            throw new RuntimeException(e);
        }
    }

    private void addWarnings(DefaultHighlighter dh, String fileName) {
        warnings.stream()
                .filter(ps -> fileName.equals(ps.fileName))
                .forEach(ps -> {
                    addWarnings(dh, ps);
                });
    }

    private void addWarnings(DefaultHighlighter dh, PositionedString ps) {
        String source = txtSource.getText();
        int offset = getOffsetFromLineColumn(source, ps.pos);
        int end = offset;
        while (end < source.length() && !Character.isWhitespace(source.charAt(end))) {
            end++;
        }
        try {
            dh.addHighlight(offset, end, new BracketMatchingTextArea.BorderPainter(Color.RED));
        } catch (BadLocationException ignore) {
            // ignore
        }
    }


    private void updateFurtherInformation(String text) {
        Pattern regex = Pattern.compile("https?://[^\\s]+");
        Matcher m = regex.matcher(text);
        if (m.find()) {
            this.urlFurtherInformation = m.group();
            btnFurtherInformation.setEnabled(true);
        } else {
            btnFurtherInformation.setEnabled(false);
        }
    }

    private boolean isJava(String fileName) {
        return fileName.endsWith(".java");
    }


    public static int getOffsetFromLineColumn(String source, Position pos) {
        return getOffsetFromLineColumn(source, pos.getLine(), pos.getColumn());
    }

    private static int getOffsetFromLineColumn(String source, int line, int column) {
        if (line < 0) throw new IllegalArgumentException();
        if (column < 0) throw new IllegalArgumentException();

        int pos = 0;
        char[] c = source.toCharArray();
        for (; pos < c.length && line > 0; ++pos) {
            if (c[pos] == '\n') {
                --line;
            }
        }
        if (line == 0) return pos + column;

        throw new ArrayIndexOutOfBoundsException("Given position is out of bounds.");
    }


    private static class PositionedStringRenderer implements ListCellRenderer<PositionedString> {
        private final JTextArea area = new JTextArea(5, 69);
        private final JPanel panel = new JPanel();

        PositionedStringRenderer() {
            area.setLineWrap(true);
            area.setWrapStyleWord(true);
            BoxLayout layout = new BoxLayout(panel, BoxLayout.Y_AXIS);
            panel.setLayout(layout);
            panel.add(area);
        }


        @Override
        public Component getListCellRendererComponent(JList<? extends PositionedString> list, PositionedString value,
                                                      int index, boolean isSelected, boolean cellHasFocus) {
            final String text = String.format("%s\n\nFilename: %s@%d:%d",
                    value.text, value.fileName, value.pos.getLine(), value.pos.getColumn());
            area.setText(text);
            area.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
            if (isSelected) {
                area.setBackground(list.getSelectionBackground());
                area.setForeground(list.getSelectionForeground());
            } else {
                area.setBackground(list.getBackground());
                area.setForeground(list.getForeground());
            }

            area.setEnabled(list.isEnabled());
            area.setFont(list.getFont());

            Border border = null;
            if (cellHasFocus) {
                if (isSelected) {
                    border = UIManager.getBorder("List.focusSelectedCellHighlightBorder");
                }
                if (border == null) {
                    border = UIManager.getBorder("List.focusCellHighlightBorder");
                }
            } else {
                border = new EmptyBorder(1, 1, 1, 1);
            }
            panel.setBorder(border);

            return panel;
        }
    }

    /*//Debugging
    public static void main(String[] args) {
            PositionedString a = new PositionedString("Multiline text\nTest\n",
                    "/home/weigl/work/key/key/key.ui/src/main/java/de/uka/ilkd/key/gui/TaskTree.java",
                    new Position(20, 25));
            PositionedString b = new PositionedString("Multiline text\nTest\n More information: https://google.de",
                    "/home/weigl/work/key/key/key.ui/src/main/java/de/uka/ilkd/key/gui/SearchBar.java",
                    new Position(35, 10));
            PositionedString c = new PositionedString("Blubb",
                    "/home/weigl/work/key/key/key.ui/src/main/java/de/uka/ilkd/key/gui/SearchBar.java",
                    new Position(36, 0));

            HashSet<PositionedString> warnings = new HashSet<>();
            warnings.add(a);
            warnings.add(b);
            warnings.add(c);
            WarningsDialog warningsDialog = new WarningsDialog(null, warnings);
            warningsDialog.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
            warningsDialog.setVisible(true);
        }*/
}
