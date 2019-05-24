package de.uka.ilkd.key.gui.nodeviews;

import javax.swing.JTextArea;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.TermLabelSV;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.NewDependingOn;
import de.uka.ilkd.key.rule.NewVarcond;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.GenericSortInstantiations;

/**
 * The methods of class TacletDescriber have been extracted from class
 * {@link InnerNodeView}. They compute the text to show for a rule application
 * which consists of the sequent including the applied rule.
 */
class TacletDescriber {

    private static void writeSVModifiers(StringBuffer out, SchemaVariable sv) {
        boolean started = false;
        if (sv.isRigid() && !(sv instanceof VariableSV)) {
            if (!started) {
                out.append("[");
            }
            out.append("rigid");
            started = true;
        }
        if (sv instanceof ProgramSV && ((ProgramSV) sv).isListSV()) {
            if (!started) {
                out.append("[");
            } else {
                out.append(", ");
            }
            out.append("list");
            started = true;
        }

        if (started) {
            out.append("]");
        }
    }

    private static void writeTacletSchemaVariable(StringBuffer out,
            SchemaVariable schemaVar) {
        if (schemaVar instanceof ModalOperatorSV) {
            final ModalOperatorSV modalOpSV = (ModalOperatorSV) schemaVar;
            String sep = "";
            for (final Operator op : modalOpSV.getModalities()) {
                out.append(sep);
                out.append(op.name());
                sep = ", ";
            }
            out.append(" } ").append(modalOpSV.name());
        } else if (schemaVar instanceof TermSV) {
            out.append("\\term");
        } else if (schemaVar instanceof FormulaSV) {
            out.append("\\formula");
        } else if (schemaVar instanceof UpdateSV) {
            out.append("\\update");
        } else if (schemaVar instanceof ProgramSV) {
            out.append("\\program");
        } else if (schemaVar instanceof VariableSV) {
            out.append("\\variables");
        } else if (schemaVar instanceof SkolemTermSV) {
            out.append("\\skolemTerm");
        } else if (schemaVar instanceof TermLabelSV) {
            out.append("\\termlabel");
        } else {
            out.append("?");
        }
        writeSVModifiers(out, schemaVar);

        /*
         * TODO: Add an explanation for the following if-statement.
         * (Kai Wallisch 01/2015)
         */
        if (!(schemaVar instanceof FormulaSV
                || schemaVar instanceof UpdateSV
                || schemaVar instanceof TermLabelSV)) {
            out.append(" ").append(schemaVar.sort().declarationString());
        }
        out.append(" ").append(schemaVar.name());
    }

    private static void writeTacletSchemaVariablesHelper(StringBuffer out,
            final Taclet t) {
        ImmutableSet<SchemaVariable> schemaVars = t.getIfFindVariables();

        for (final NewVarcond nvc: t.varsNew()) {
            schemaVars = schemaVars.add(nvc.getSchemaVariable());
        }

        for (final NewDependingOn ndo : t.varsNewDependingOn()) {
            schemaVars = schemaVars.add(ndo.first());
        }

        if (!schemaVars.isEmpty()) {
            out.append("\\schemaVariables {\n");
            for (SchemaVariable schemaVar1 : schemaVars) {
                final SchemaVariable schemaVar = schemaVar1;
                // write indentation
                out.append("  ");
                // write declaration
                writeTacletSchemaVariable(out, schemaVar);
                // write newline
                out.append(";\n");
            }
            out.append("}\n");
        }
    }

    /**
     * <p>
     * Computes the text to show in this {@link JTextArea} which consists of the
     * sequent including the applied rule.
     * </p>
     * <p>
     * This information is also relevant for other tools like the Symbolic
     * Execution Debugger.
     * </p>
     *
     * @param mediator The {@link KeYMediator} to use.
     * @param node The {@link Node} to use.
     * @param filter The {@link SequentPrintFilter} to use.
     * @return The text to show.
     */
    public static String getTacletDescription(KeYMediator mediator,
            Node node,
            SequentPrintFilter filter) {

        RuleApp app = node.getAppliedRuleApp();
        String s = "";

        if (app != null) {
            s += "The following rule was applied on this node: \n\n";
            if (app.rule() instanceof Taclet) {
                SequentViewLogicPrinter logicPrinter = new SequentViewLogicPrinter(new ProgramPrinter(null),
                        mediator.getNotationInfo(),
                        mediator.getServices(),
                        true,
                        getVisibleTermLabels());
                logicPrinter.printTaclet((Taclet) (app.rule()));
                s += logicPrinter;
            } else {
                s = s + app.rule();
            }

            if (app instanceof TacletApp) {
                TacletApp tapp = (TacletApp) app;
                if (tapp.instantiations().getGenericSortInstantiations()
                        != GenericSortInstantiations.EMPTY_INSTANTIATIONS) {
                    s = s + "\n\nWith sorts:\n";
                    s = s
                            + tapp.instantiations().getGenericSortInstantiations();
                }

                StringBuffer sb = new StringBuffer("\n\n");
                writeTacletSchemaVariablesHelper(sb, tapp.taclet());
                s = s + sb;
            }

//                  s = s + "\n\nApplication justified by: ";
//                  s = s + mediator.getSelectedProof().env().getJustifInfo()
//                                      .getJustification(app, mediator.getServices())+"\n";
        } else {
            // Is this case possible?
            s += "No rule was applied on this node.";
        }
        return s;
    }

    private static VisibleTermLabels getVisibleTermLabels() {
        return MainWindow.getInstance().getVisibleTermLabels();
    }

}
