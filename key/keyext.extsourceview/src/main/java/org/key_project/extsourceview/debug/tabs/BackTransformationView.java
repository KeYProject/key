package org.key_project.extsourceview.debug.tabs;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.sourceview.SourceView;
import de.uka.ilkd.key.gui.sourceview.SourceViewInsertion;
import org.key_project.extsourceview.debug.DebugTab;
import org.key_project.extsourceview.transformer.InternTransformException;
import org.key_project.extsourceview.transformer.TransformException;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.*;
import java.util.stream.Collectors;

public class BackTransformationView extends DebugTab {

    private JTextArea taSource;

    public BackTransformationView(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        super();

        initGUI();
    }

    private void initGUI() {
        setLayout(new BorderLayout());

        var pnlConf = new JPanel(new GridBagLayout());

        {
            var ctrl = new JRadioButton("Position at Start+End", true);
            pnlConf.add(ctrl, gbc(0, 0));
            ctrl.addItemListener(e -> { /* TODO */ });
        }
        {
            var ctrl = new JRadioButton("Position at logical pos", false);
            pnlConf.add(ctrl, gbc(0, 1));
            ctrl.addItemListener(e -> { /* TODO */ });
        }

        this.add(pnlConf, BorderLayout.NORTH);

        taSource = new JTextArea();
        taSource.setEditable(false);
        taSource.setFont(new Font("Courier New", Font.PLAIN, 12));
        taSource.setLineWrap(true);

        this.add(new JScrollPane(taSource), BorderLayout.CENTER);
    }

    private static GridBagConstraints gbc(int x, int y) {
        return new GridBagConstraints
        (
            x, y,
            1, 1,
            1.0 , 1.0,
            GridBagConstraints.CENTER,
            GridBagConstraints.BOTH,
            new Insets(0, 0, 0, 0),
            0, 0
        );
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