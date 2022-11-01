package org.key_project.extsourceview.debug.tabs;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.gui.sourceview.SourceViewInsertion;
import org.key_project.extsourceview.ExtSourceViewExtension;
import org.key_project.extsourceview.debug.DebugTab;
import org.key_project.extsourceview.transformer.InternTransformException;
import org.key_project.extsourceview.transformer.TransformException;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.*;
import java.util.stream.Collectors;

import static org.key_project.extsourceview.debug.tabs.GUIUtil.gbc;

public class BackTransformationView extends DebugTab {

    private JTextArea taSource;

    public BackTransformationView(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        super();

        initGUI(window, mediator);
    }

    private void initGUI(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        setLayout(new BorderLayout());

        var pnlConf = new JPanel(new GridBagLayout());

        {
            var ctrl = new JRadioButton("Position at Start+End", true);
            pnlConf.add(ctrl, gbc(0, 0));
            ctrl.addActionListener(e -> { /* TODO */ });
        }
        {
            var ctrl = new JRadioButton("Position at logical pos", false);
            pnlConf.add(ctrl, gbc(0, 1));
            ctrl.addActionListener(e -> { /* TODO */ });
        }
        {
            var cbx = new JCheckBox("Show all InsTerms", false);
            pnlConf.add(cbx, gbc(0, 2));
            cbx.addItemListener(e -> {
                ExtSourceViewExtension.Inst.HideNonRelevantTerms = !cbx.isSelected();
                ExtSourceViewExtension.Inst.update(window, mediator);
            });
        }
        {
            var ctrl = new JButton("Retry");
            pnlConf.add(ctrl, gbc(2, 0, 1, 3));
            ctrl.addActionListener(e -> ExtSourceViewExtension.Inst.update(window, mediator));
        }

        this.add(pnlConf, BorderLayout.NORTH);

        taSource = new JTextArea();
        taSource.setEditable(false);
        taSource.setFont(new Font("Courier New", Font.PLAIN, 12));
        taSource.setLineWrap(true);

        this.add(new JScrollPane(taSource), BorderLayout.CENTER);
    }

    @Nonnull
    @Override
    public String getTitle() {
        return "Transformer";
    }

    public void clearStatus() {
        taSource.setBackground(Color.WHITE);
        taSource.setText("");
    }

    public void setStatusFailure(TransformException e) {
        taSource.setBackground(new Color(255, 208, 121));
        taSource.setText(String.format("[FAILED TO TRANSFORM]\n\n%s\n\n--------------------------------\n\n%s", e.getMessage(), e));
    }

    public void setStatusException(InternTransformException e) {
        taSource.setBackground(new Color(255, 125, 125));
        taSource.setText(String.format("[EXCEPTION]\n\n%s\n\n--------------------------------\n\n%s", e.getMessage(), e));
    }
}