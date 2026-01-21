package org.key_project.extsourceview.debug.tabs;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.origin.OriginRef;
import org.key_project.extsourceview.ExtSourceViewExtension;
import org.key_project.extsourceview.debug.DebugTab;
import org.key_project.extsourceview.transformer.*;

import org.jspecify.annotations.NonNull;
import javax.swing.*;
import java.awt.*;
import java.util.function.Consumer;
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

    private boolean showErrorsInline = true;

    private final MainWindow mainWindow;

    public BackTransformationView(@NonNull MainWindow window, @NonNull KeYMediator mediator) {
        super();

        mainWindow = window;

        initGUI(window, mediator);
    }

    private void initGUI(@NonNull MainWindow window, @NonNull KeYMediator mediator) {
        setLayout(new BorderLayout());

        var pnlConf = new JPanel(new GridBagLayout());

        {
            var cbx = new JCheckBox("Enabled", true);
            pnlConf.add(cbx, gbcf(0, 0));
            cbx.addItemListener(e -> {
                refresh.accept(false);
                mainWindow.getSourceViewFrame().getSourceView().setErrorDisplay(Color.WHITE, "");
                mainWindow.getSourceViewFrame().getSourceView().setInfoDisplay(Color.WHITE, "");
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.TransformerEnabled = cbx.isSelected());
        }
        {
            var cbx = new JCheckBox("Inline Errors", true);
            pnlConf.add(cbx, gbcf(0, 1));
            cbx.addItemListener(e -> {
                refresh.accept(false);
                mainWindow.getSourceViewFrame().getSourceView().setErrorDisplay(Color.WHITE, "");
                mainWindow.getSourceViewFrame().getSourceView().setInfoDisplay(Color.WHITE, "");
            });
            refresh = refresh.andThen(v -> BackTransformationView.this.showErrorsInline = cbx.isSelected());
        }
        {
            var ctrl = new JComboBox<>(new String[]{
                "Position at {1}",
                "Position at method start+end",
                "Position at heap-origin pos",
                "Position Algorithm v2",
            });
            ctrl.setSelectedIndex(ExtSourceViewExtension.Inst.PositioningStrategy);
            pnlConf.add(ctrl, gbcf(0, 5));
            ctrl.addActionListener(e -> {
                ExtSourceViewExtension.Inst.PositioningStrategy = ctrl.getSelectedIndex();
                refresh.accept(false);
            });
        }
        {
            var ctrl = new JComboBox<>(new String[]{
                    "Leave scroll untouched",
                    "Try to persist raw line",
                    "Autom scroll to ActiveStatement",
            });
            ctrl.setSelectedIndex(ExtSourceViewExtension.Inst.ScrollFixMode);
            pnlConf.add(ctrl, gbcf(0, 6));
            ctrl.addActionListener(e -> {
                ExtSourceViewExtension.Inst.ScrollFixMode = ctrl.getSelectedIndex();
                refresh.accept(false);
            });
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
            var cbx = new JCheckBox("Colorize Insertions", true);
            pnlConf.add(cbx, gbcf(2, 2));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.ColorizedInsTerms = cbx.isSelected());
        }
        {
            var cbx = new JCheckBox("Show extended interactions", false);
            pnlConf.add(cbx, gbcf(2, 5));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.ShowExtInteractions = cbx.isSelected());
        }
        {
            var cbx = new JCheckBox("Allow untagged formulas", true);
            pnlConf.add(cbx, gbcf(3, 0));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.AllowUntaggedFormulas = cbx.isSelected());
        }
        {
            var cbx = new JCheckBox("No Translation Fallback", false);
            pnlConf.add(cbx, gbcf(3, 1));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.NoTranslationFallback = cbx.isSelected());
        }
        {
            var cbx = new JCheckBox("Recursive Origin Lookup", false);
            pnlConf.add(cbx, gbcf(3, 2));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.RecursiveOriginLookup = cbx.isSelected());
        }
        {
            var cbx = new JCheckBox("Allow unknown constants", true);
            pnlConf.add(cbx, gbcf(3, 3));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.AllowUnknownConstants = cbx.isSelected());
        }
        {
            var cbx = new JCheckBox("Allow disjunct assertions", true);
            pnlConf.add(cbx, gbcf(3, 4));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.AllowDisjunctAssertions = cbx.isSelected());
        }
        {
            var cbx = new JCheckBox("Re-inline pulled out terms", true);
            pnlConf.add(cbx, gbcf(3, 5));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.ReInlineConstPullouts = cbx.isSelected());
        }
        {
            var cbx = new JCheckBox("Manually translate loop assertion", true);
            pnlConf.add(cbx, gbcf(3, 6));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.ManuallyTranslateLoopAssertions = cbx.isSelected());
        }
        {
            var ctrl = new JButton("Retry");
            pnlConf.add(ctrl, gbcf(4, 0, 1, 2));
            ctrl.addActionListener(e -> refresh.accept(false));
        }
        {
            var cbx = new JCheckBox("Fail on Categorization", true);
            pnlConf.add(cbx, gbcf(4, 2));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.FailOnCategorization = cbx.isSelected());
        }
        {
            var cbx = new JCheckBox("Fail on Translation", false);
            pnlConf.add(cbx, gbcf(4, 3));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.FailOnTranslation = cbx.isSelected());
        }
        {
            var cbx = new JCheckBox("Fail on Positioning", true);
            pnlConf.add(cbx, gbcf(4, 4));
            cbx.addItemListener(e -> {
                refresh.accept(false);
            });
            refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.FailOnPositioning = cbx.isSelected());
        }

        pnlConf.setMinimumSize(new Dimension(0, 0));

        this.add(pnlConf, BorderLayout.NORTH);

        taSource = new JTextArea();
        taSource.setEditable(false);
        taSource.setFont(new Font("Courier New", Font.PLAIN, 12));
        taSource.setLineWrap(true);

        this.add(new JScrollPane(taSource), BorderLayout.CENTER);

        refresh.accept(true);
        refresh = refresh.andThen(v -> ExtSourceViewExtension.Inst.update(window, mediator));
    }

    @NonNull
    @Override
    public String getTitle() {
        return "Transformer";
    }

    public void clearStatus() {
        taSource.setBackground(Color.WHITE);
        taSource.setText("");

        mainWindow.getSourceViewFrame().getSourceView().setErrorDisplay(Color.WHITE, "");
        mainWindow.getSourceViewFrame().getSourceView().setInfoDisplay(Color.WHITE, "");
    }

    public void setStatusFailure(Services svc, Sequent sequent, TransformException e) {
        taSource.setBackground(new Color(255, 208, 121));

        var fileUri = mainWindow.getSourceViewFrame().getSourceView().getSelectedFile();

        if (e instanceof TermTransformException) {
            var tte = (TermTransformException)e;
            taSource.setText(String.format(
                    "[FAILED TO TRANSFORM]\n\n%s"+
                    "\n\n--------------------------------\n\n%s"+
                    "\n\n--------------------------------\n\n%s"+
                    "\n\n--------------------------------\n\n%s",
                    e.getMessage(),
                    tte.Term.getOriginRef().stream().map(OriginRef::toString).collect(Collectors.joining("\n")),
                    (new TermTranslator(fileUri, svc, sequent, true, true, false)).translateSafe(tte.Term, InsertionType.ASSERT),
                    e));
        } else {
            taSource.setText(String.format(
                    "[FAILED TO TRANSFORM]\n\n%s\n%s\n\n--------------------------------\n\n%s",
                    e.getMessage(),
                    e.Extra,
                    e));
        }

        if (showErrorsInline) {
            mainWindow.getSourceViewFrame().getSourceView().setInfoDisplay(new Color(255, 128, 0), e.getMessage());
        }
    }

    public void setStatusException(InternTransformException e) {
        taSource.setBackground(new Color(255, 125, 125));
        taSource.setText(String.format(
            "[EXCEPTION]\n\n%s\n\n--------------------------------\n\n%s", e.getMessage(), e));

        if (showErrorsInline) {
            mainWindow.getSourceViewFrame().getSourceView().setErrorDisplay(new Color(255, 64, 64), "Fatal Exception while transforming current Sequent");
        }
    }
}
