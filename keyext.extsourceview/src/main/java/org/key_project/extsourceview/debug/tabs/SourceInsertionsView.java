package org.key_project.extsourceview.debug.tabs;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.gui.sourceview.SourceViewInsertion;
import org.key_project.extsourceview.debug.DebugTab;

import org.jspecify.annotations.NonNull;
import javax.swing.*;
import java.awt.*;
import java.util.stream.Collectors;

import static org.key_project.extsourceview.debug.tabs.GUIUtil.gbc;

/**
 * Class for the [Source Insertions] Tab in the debug panel
 *
 * Displays a list of all current insertions in the SourceView
 * And also can be used to add/clear custom insertions
 */
public class SourceInsertionsView extends DebugTab {

    private final SourceView sourceView;

    public SourceInsertionsView(@NonNull MainWindow window, @NonNull KeYMediator mediator) {
        super();

        sourceView = window.getSourceViewFrame().getSourceView();

        initGUI(sourceView);
    }

    private void initGUI(SourceView sv) {
        setLayout(new BorderLayout());

        var pnl = new JPanel(new GridBagLayout());

        JTextField ed0 = new JTextField("debug");
        JTextField ed1 = new JTextField("3");
        JTextField ed2 = new JTextField("    " + "    " + "Some Text");
        ed2.setFont(Font.getFont("Courier New"));
        JButton btn1 = new JButton("Add Insertion");
        btn1.addActionListener((e) -> addInsertion(ed0.getText(), ed1.getText(), ed2.getText()));
        JButton btn2 = new JButton("Clear Insertion");
        btn2.addActionListener((e) -> clearInsertions(ed0.getText()));

        pnl.add(new JLabel("Group: "), gbc(0, 0));
        pnl.add(ed0, gbc(1, 0));

        pnl.add(new JLabel("Line: "), gbc(0, 1));
        pnl.add(ed1, gbc(1, 1));

        pnl.add(new JLabel("Text: "), gbc(0, 2));
        pnl.add(ed2, gbc(1, 2));

        pnl.add(btn1, gbc(0, 3, 2, 1));
        pnl.add(btn2, gbc(0, 4, 2, 1));

        pnl.setMinimumSize(new Dimension(0, 0));

        add(pnl, BorderLayout.NORTH);

        var dlm = new DefaultListModel<String>();
        var list = new JList<>(dlm);

        Runnable refresh = () -> {
            try {
                var data = this.sourceView.listInsertion(this.sourceView.getSelectedFile()).stream()
                        .map(p -> String.format("[%s] {=> %d} '%s'", p.Group, p.Line, p.Text))
                        .collect(Collectors.toList());
                dlm.clear();
                dlm.addAll(data);
            } catch (Exception ex) {
                dlm.clear();
                dlm.addElement(ex.toString());
            }
        };

        list.setFont(Font.getFont("Courier New"));

        sv.addInsertionChangedListener(refresh::run);

        add(new JScrollPane(list), BorderLayout.CENTER);
    }

    private void clearInsertions(String grp) {
        try {

            sourceView.clearInsertion(sourceView.getSelectedFile(), grp);

        } catch (Exception e) {
            JOptionPane.showMessageDialog(SourceInsertionsView.this, e.toString());
        }
    }

    private void addInsertion(String grp, String pos, String text) {
        try {
            int intpos = Integer.parseInt(pos);

            SourceViewInsertion ins = new SourceViewInsertion(grp, intpos, text, Color.BLACK, new Color(111, 111, 222), null);

            ins.addClickListener(e -> JOptionPane.showMessageDialog(null, "[LeftClick]\n" + text));
            ins.addRightClickListener(
                e -> JOptionPane.showMessageDialog(null, "[RightClick]\n" + text));

            ins.addMouseEnterListener(e -> System.out.println("[ENTER] " + text));
            ins.addMouseMoveListener(e -> System.out.println("[MOVE]  " + text));
            ins.addMouseLeaveListener(e -> System.out.println("[LEAVE] " + text));

            sourceView.addInsertion(sourceView.getSelectedFile(), ins);

        } catch (Exception e) {
            JOptionPane.showMessageDialog(SourceInsertionsView.this, e.toString());
        }
    }

    @NonNull
    @Override
    public String getTitle() {
        return "Source Insertions";
    }
}
