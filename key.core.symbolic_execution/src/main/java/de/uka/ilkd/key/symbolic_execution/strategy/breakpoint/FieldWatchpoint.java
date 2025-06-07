/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.strategy.breakpoint;

import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;

/**
 * This{@link FieldWatchpoint} represents a Java watchpoint and is responsible to tell the debugger
 * to stop execution when the respective variable is accessed or modified.
 *
 * @author Marco Drebing
 */
public class FieldWatchpoint extends AbstractHitCountBreakpoint {
    private boolean isAccess;

    private boolean isModification;

    private final String fullFieldName;

    /**
     * Creates a new {@link FieldWatchpoint}.
     *
     * @param enabled flag if the Breakpoint is enabled
     * @param hitCount the number of hits after which the execution should hold at this breakpoint
     * @param fieldName the field to watch
     * @param isAcces flag to watch for accesses
     * @param isModification flag to watch for modifications
     * @param containerKJT the type of the element containing the breakpoint
     * @param proof the {@link Proof} that will be executed and should stop
     */
    public FieldWatchpoint(boolean enabled, int hitCount, String fieldName, boolean isAcces,
            boolean isModification, KeYJavaType containerKJT, Proof proof) {
        super(hitCount, proof, enabled);
        this.isAccess = isAcces;
        this.isModification = isModification;
        this.fullFieldName = containerKJT.getSort().toString() + "::" + fieldName;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isBreakpointHit(SourceElement activeStatement, RuleApp ruleApp, Node node) {
        if (activeStatement instanceof Assignment assignment) {
            SourceElement firstElement = assignment.getChildAt(0);
            if (firstElement instanceof FieldReference) {
                PosInOccurrence pio = ruleApp.posInOccurrence();
                JTerm t = (JTerm) pio.subTerm();
                if (((FieldReference) firstElement).getProgramVariable().name().toString()
                        .equals(fullFieldName) && isModification && hitcountExceeded(node)) {
                    return super.isBreakpointHit(activeStatement, ruleApp, node);
                }
            }
            if (checkChildrenOfSourceElement(assignment) && hitcountExceeded(node)) {
                return super.isBreakpointHit(activeStatement, ruleApp, node);
            }
        } else if (activeStatement != null) {
            if (checkChildrenOfSourceElement(activeStatement) && hitcountExceeded(node)) {
                return super.isBreakpointHit(activeStatement, ruleApp, node);
            }
        }
        return false;
    }

    private boolean checkChildrenOfSourceElement(SourceElement sourceElement) {
        boolean found = false;
        if (sourceElement instanceof Assignment assignment) {
            for (int i = 1; i < assignment.getChildCount(); i++) {
                SourceElement childElement = assignment.getChildAt(i);
                if (childElement instanceof FieldReference field && field
                        .getProgramVariable().name().toString().equals(fullFieldName)) {
                    ProgramVariable progVar = field.getProgramVariable();
                    if (fullFieldName.equals(progVar.toString())) {
                        return isAccess;
                    }
                } else if (childElement instanceof NonTerminalProgramElement) {
                    found = found || checkChildrenOfSourceElement(childElement);
                }
            }
        } else if (sourceElement instanceof NonTerminalProgramElement programElement) {
            for (int i = 0; i < programElement.getChildCount(); i++) {
                SourceElement childElement = programElement.getChildAt(i);
                if (childElement instanceof FieldReference field && field
                        .getProgramVariable().name().toString().equals(fullFieldName)) {
                    ProgramVariable progVar = field.getProgramVariable();
                    if (fullFieldName.equals(progVar.toString())) {
                        return isAccess;
                    }
                } else if (childElement instanceof NonTerminalProgramElement) {
                    found = found || checkChildrenOfSourceElement(childElement);
                }
            }
        }
        return found;
    }

    /**
     * @return the isAccess
     */
    public boolean isAccess() {
        return isAccess;
    }

    /**
     * @param isAccess the isAccess to set
     */
    public void setAccess(boolean isAccess) {
        this.isAccess = isAccess;
    }

    /**
     * @return the isModification
     */
    public boolean isModification() {
        return isModification;
    }

    /**
     * @param isModification the isModification to set
     */
    public void setModification(boolean isModification) {
        this.isModification = isModification;
    }
}
