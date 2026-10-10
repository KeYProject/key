/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Label;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.visitor.FreeLabelFinder;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;


/**
 * A variable condition for the taclet construct {@code \freeLabelIn}, checking whether a program
 * label occurs freely in a Java program (block).
 *
 * @author Michael Kirsten
 */
public final class FreeLabelInVariableCondition extends VariableConditionAdapter {

    private final SchemaVariable label;
    private final SchemaVariable statement;
    private final boolean negated;
    private final FreeLabelFinder freeLabelFinder = new FreeLabelFinder();

    /**
     * Instantiates a new free-label-in condition.
     *
     * @param label the schema variable which must be instantiated with a program label
     * @param statement the schema variable which must be instantiated with a program element
     *        (statement)
     * @param negated whether the condition is negated ({@code \not freeLabelIn})
     */
    public FreeLabelInVariableCondition(SchemaVariable label, SchemaVariable statement,
            boolean negated) {
        this.label = label;
        this.statement = statement;
        this.negated = negated;
    }


    @Override
    public boolean check(SchemaVariable var, SyntaxElement instCandidate, SVInstantiations instMap,
            Services services) {
        Label prgLabel = null;
        ProgramElement program = null;

        if (var == label) {
            prgLabel = (Label) instCandidate;
            program = (ProgramElement) instMap.getInstantiation(statement);
        } else if (var == statement) {
            prgLabel = (Label) instMap.getInstantiation(label);
            program = (ProgramElement) instCandidate;
        }

        if (program == null || prgLabel == null) {
            // not yet complete or not responsible
            return true;
        }

        final boolean freeIn = freeLabelFinder.findLabel(prgLabel, program);
        return negated != freeIn;
    }


    @Override
    public String toString() {
        return (negated ? "\\not" : "") + "\\freeLabelIn (" + label.name() + "," + statement.name()
            + ")";
    }
}
