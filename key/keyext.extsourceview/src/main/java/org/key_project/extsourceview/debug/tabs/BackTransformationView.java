package org.key_project.extsourceview.debug.tabs;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.origin.OriginRef;
import org.key_project.extsourceview.ExtSourceViewExtension;
import org.key_project.extsourceview.debug.DebugTab;
import org.key_project.extsourceview.transformer.InternTransformException;
import org.key_project.extsourceview.transformer.TermTransformException;
import org.key_project.extsourceview.transformer.TermTranslator;
import org.key_project.extsourceview.transformer.TransformException;

import javax.annotation.Nonnull;
import javax.swing.*;
import java.awt.*;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;

import static org.key_project.extsourceview.debug.tabs.GUIUtil.gbc;
import static org.key_project.extsourceview.debug.tabs.GUIUtil.gbcf;

/**
 * Class for the [Transformer] Tab in the debug panel
 *
 * Used to display errors in the back-transformation step
 * And to configure it.
 */
public class BackTransformationView extends DebugTab {

    private JTextArea taSource;

    private Consumer<Boolean> refresh = ((v) -> {});

    public BackTransformationView(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        super();

        initGUI(window, mediator);
    }

    private void initGUI(@Nonnull MainWindow window, @Nonnull KeYMediator mediator) {
        setLayout(new BorderLayout());

        var pnlConf = new JPanel(new GridBagLayout());

        {
            var cbx = new JCheckBox("Enabled", true);
            pnlConf.add(cbx, gbcf(0, 0));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.TransformerEnabled = cbx.isSelected());
        }
        {
            var ctrl = new JRadioButton("Position at method start+end", false);
            pnlConf.add(ctrl, gbcf(0, 1));
            ctrl.addActionListener(e -> {
                ExtSourceViewExtension.Inst.PositioningStrategy = 0;
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ctrl.setSelected(ExtSourceViewExtension.Inst.PositioningStrategy == 0));
        }
        {
            var ctrl = new JRadioButton("Position at heap-origin pos", true);
            pnlConf.add(ctrl, gbcf(0, 2));
            ctrl.addActionListener(e -> {
                ExtSourceViewExtension.Inst.PositioningStrategy = 1;
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ctrl.setSelected(ExtSourceViewExtension.Inst.PositioningStrategy == 1));
        }
        {
            pnlConf.add(Box.createHorizontalGlue(), gbc(1, 0)); // spacer
            pnlConf.add(Box.createHorizontalGlue(), gbc(1, 1)); // spacer
        }
        {
            var cbx = new JCheckBox("Show all InsTerms", false);
            pnlConf.add(cbx, gbcf(2, 1));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.ShowNonRelevantTerms = cbx.isSelected());
        }
        {
            var cbx = new JCheckBox("Fail on unknown terms", true);
            pnlConf.add(cbx, gbcf(2, 2));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.FailOnError = cbx.isSelected());
        }
        {
            var cbx = new JCheckBox("Recursive Origin Lookup", false);
            pnlConf.add(cbx, gbcf(3, 1));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.RecursiveOriginLookup = cbx.isSelected());
        }
        {
            var cbx = new JCheckBox("Allow untagged formulas", true);
            pnlConf.add(cbx, gbcf(3, 2));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.AllowUntaggedFormulas = cbx.isSelected());
        }
        {
            var cbx = new JCheckBox("No Translation Fallback", false);
            pnlConf.add(cbx, gbcf(4, 2));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.NoTranslationFallback = cbx.isSelected());
        }
        {
            var ctrl = new JButton("Retry");
            pnlConf.add(ctrl, gbcf(5, 1, 1, 2));
            ctrl.addActionListener(e -> refresh.accept(false));
        }

        this.add(pnlConf, BorderLayout.NORTH);

        taSource = new JTextArea();
        taSource.setEditable(false);
        taSource.setFont(new Font("Courier New", Font.PLAIN, 12));
        taSource.setLineWrap(true);

        this.add(new JScrollPane(taSource), BorderLayout.CENTER);

        refresh.accept(true);
        refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.update(window, mediator));
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

    public void setStatusFailure(Services svc, TransformException e) {
        taSource.setBackground(new Color(255, 208, 121));
        if (e instanceof TermTransformException) {
            var tte = (TermTransformException)e;
            taSource.setText(String.format(
                    "[FAILED TO TRANSFORM]\n\n%s"+
                    "\n\n--------------------------------\n\n%s"+
                    "\n\n--------------------------------\n\n%s"+
                    "\n\n--------------------------------\n\n%s",
                    e.getMessage(),
                    tte.Term.getOriginRef().stream().map(OriginRef::toString).collect(Collectors.joining("\n")),
                    (new TermTranslator(svc, true)).translateSafe(tte.Term),
                    e));
        } else {
            taSource.setText(String.format(
                    "[FAILED TO TRANSFORM]\n\n%s\n\n--------------------------------\n\n%s",
                    e.getMessage(),
                    e));
        }
    }

    public void setStatusException(InternTransformException e) {
        taSource.setBackground(new Color(255, 125, 125));
        taSource.setText(String.format(
            "[EXCEPTION]\n\n%s\n\n--------------------------------\n\n%s", e.getMessage(), e));
    }
}
