/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.pp.VisibleTermLabels;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.GenericSortInstantiations;

import org.key_project.util.collection.ImmutableSet;

/**
 * The methods of class TacletDescriber have been extracted from class {@link InnerNodeView}. They
 * compute the text to show for a rule application which consists of the sequent including the
 * applied rule.
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

    private static void writeTacletSchemaVariable(StringBuffer out, SchemaVariable schemaVar) {
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
         * TODO: Add an explanation for the following if-statement. (Kai Wallisch 01/2015)
         */
        if (!(schemaVar instanceof FormulaSV || schemaVar instanceof UpdateSV
                || schemaVar instanceof TermLabelSV)) {
            out.append(" ").append(schemaVar.sort().declarationString());
        }
        out.append(" ").append(schemaVar.name());
    }

    private static void writeTacletSchemaVariablesHelper(StringBuffer out, final Taclet t) {
        ImmutableSet<SchemaVariable> schemaVars = t.getIfFindVariables();

        for (final NewVarcond nvc : t.varsNew()) {
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
     * Computes the text to show in this {@link JTextArea} which consists of the sequent including
     * the applied rule.
     * </p>
     * <p>
     * This information is also relevant for other tools like the Symbolic Execution Debugger.
     * </p>
     *
     * @param mediator The {@link KeYMediator} to use.
     * @param app The {@link RuleApp} to use.
     * @return The text to show.
     */
    public static String getTacletDescription(KeYMediator mediator, RuleApp app, int width) {
        StringBuilder s = new StringBuilder();

        if (app != null) {
            s.append("The following rule was applied on this node: \n\n");
            if (app.rule() instanceof Taclet) {
                SequentViewLogicPrinter logicPrinter =
                    SequentViewLogicPrinter.purePrinter(width, mediator.getNotationInfo(),
                        mediator.getServices(), getVisibleTermLabels());
                logicPrinter.printTaclet((Taclet) (app.rule()));
                s.append(logicPrinter.result());
            } else {
                s.append(app.rule());
            }

            if (app instanceof TacletApp) {
                TacletApp tapp = (TacletApp) app;
                if (tapp.instantiations()
                        .getGenericSortInstantiations() != GenericSortInstantiations.EMPTY_INSTANTIATIONS) {
                    s.append("\n\nWith sorts:\n");
                    s.append(tapp.instantiations().getGenericSortInstantiations());
                }
                // Removed call to writeTacletSchemaVariablesHelper since schema vars are printed by
                // the logic printer
            }
        } else {
            // Is this case possible?
            s.append("No rule was applied on this node.");
        }
        return s.toString();
    }

    private static VisibleTermLabels getVisibleTermLabels() {
        return MainWindow.getInstance().getVisibleTermLabels();
    }

}
