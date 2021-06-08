package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.sourceview.JavaDocument;
import de.uka.ilkd.key.gui.sourceview.TextLineNumber;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.SLEnvInput;
import de.uka.ilkd.key.util.Debug;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.IOUtil;
import sun.swing.DefaultLookup;

import javax.swing.*;
import javax.swing.border.Border;
import javax.swing.border.EmptyBorder;
import javax.swing.text.BadLocationException;
import javax.swing.text.SimpleAttributeSet;
import java.awt.*;
import java.awt.event.KeyEvent;
import java.io.IOException;
import java.io.InputStream;
import java.util.HashMap;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (6/8/21)
 */
public class WarningsDialog extends JDialog {
    private final Map<String, String> fileContentsCache = new HashMap<>();
    private final JTextArea txtSource = new JTextArea(10, 69);
    private final JList<PositionedString> listWarnings;

    public WarningsDialog(Frame owner, ImmutableSet<PositionedString> warnings) {
        super(owner, SLEnvInput.getLanguage() + " warning(s)", true);
        setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);

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

        listWarnings = new JList<>(warnings.toArray(new PositionedString[warnings.size()]));
        listWarnings.addListSelectionListener(e -> updatePreview());
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

        txtSource.setFont(UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW));
        txtSource.setEditable(false);

        final JButton btnOk = new JButton("OK");
        btnOk.addActionListener(e -> setVisible(false));
        Dimension buttonDim = new Dimension(100, 27);
        btnOk.setPreferredSize(buttonDim);
        btnOk.setMinimumSize(buttonDim);
        JPanel pButtons = new JPanel();
        pButtons.add(btnOk);
        add(pButtons, BorderLayout.SOUTH);
        getRootPane().setDefaultButton(btnOk);

        btnOk.registerKeyboardAction(
                event -> {
                    if (event.getActionCommand().equals("ESC")) {
                        btnOk.doClick();
                    }
                },
                "ESC",
                KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
                JComponent.WHEN_IN_FOCUSED_WINDOW);

        splitCenter.setDividerLocation(.5);
    }

    private void updatePreview() {
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
            try {
                JavaDocument doc = new JavaDocument();
                txtSource.setDocument(doc);
                doc.insertString(0, source, new SimpleAttributeSet());
            } catch (BadLocationException e) {
                throw new AssertionError();
            }
        } else {
            txtSource.setText(source);
        }


        txtSource.setEditable(false);
        int offset = getOffsetFromLineColumn(source, ps.pos);
        txtSource.setCaretPosition(offset);
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

}

class PositionedStringRenderer implements ListCellRenderer<PositionedString> {
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
        //int newlines = (int) text.chars().filter(it -> it == '\n').count();
        area.setText(text);
        //area.setRows(newlines);

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
                border = DefaultLookup.getBorder(area, area.getUI(), "List.focusSelectedCellHighlightBorder");
            }
            if (border == null) {
                border = DefaultLookup.getBorder(area, area.getUI(), "List.focusCellHighlightBorder");
            }
        } else {
            border = new EmptyBorder(1, 1, 1, 1);
        }
        area.setBorder(border);

        return panel;
    }

    /* mockup
    public static void main(String[] args) {
        PositionedString a = new PositionedString("Multiline text\nTest\n",
                "/home/weigl/work/key/key/key.ui/src/main/java/de/uka/ilkd/key/gui/TaskTree.java",
                new Position(20, 25));
        PositionedString b = new PositionedString("Multiline text\nTest\n",
                "/home/weigl/work/key/key/key.ui/src/main/java/de/uka/ilkd/key/gui/SearchBar.java",
                new Position(35, 69));

        ImmutableSet<PositionedString> warnings =
                DefaultImmutableSet.fromImmutableList(ImmutableSLList.singleton(a).append(b));
        WarningsDialog warningsDialog = new WarningsDialog(null, warnings);
        warningsDialog.pack();

        warningsDialog.setVisible(true);
    }
     */
}