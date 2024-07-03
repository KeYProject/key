/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package org.key_project.ui.interactionlog.model;

import java.util.List;
import java.util.stream.Collectors;
import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlRootElement;
import javax.xml.bind.annotation.XmlTransient;

import de.uka.ilkd.key.api.ProofMacroApi;
import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * @author Alexander Weigl
 */
@XmlRootElement()
@XmlAccessorType(XmlAccessType.FIELD)
public final class MacroInteraction extends NodeInteraction {
    private static final long serialVersionUID = 1L;

    private String macroName;

    @XmlTransient
    private ProofMacro macro;
    @XmlTransient
    private PosInOccurrence pos;

    private String info;

    private List<Integer> openGoalSerialNumbers;
    private List<NodeIdentifier> openGoalNodeIds;

    public MacroInteraction() {
    }

    public MacroInteraction(Node node, ProofMacro macro,
            PosInOccurrence posInOcc, ProofMacroFinishedInfo info) {
        super(node);
        this.macroName = macro.getScriptCommandName();
        this.pos = posInOcc;
        this.info = info == null ? "" : info.toString();

        ImmutableList<Goal> openGoals =
            info != null && info.getProof() != null ? info.getProof().openGoals()
                    : ImmutableSLList.<Goal>nil();
        this.openGoalSerialNumbers =
            openGoals.stream().map(g -> g.node().serialNr()).collect(Collectors.toList());
        this.openGoalNodeIds =
            openGoals.stream().map(g -> NodeIdentifier.get(g.node())).collect(Collectors.toList());
    }

    @Override
    public String toString() {
        return macroName;
    }

    public String getMacro() {
        return macroName;
    }

    public void setMacro(ProofMacro macro) {
        this.macro = macro;
    }

    public PosInOccurrence getPos() {
        return pos;
    }

    public void setPos(PosInOccurrence pos) {
        this.pos = pos;
    }

    public String getInfo() {
        return info;
    }

    public void setInfo(String info) {
        this.info = info;
    }

    public List<Integer> getOpenGoalSerialNumbers() {
        return openGoalSerialNumbers;
    }

    public void setOpenGoalSerialNumbers(List<Integer> openGoalSerialNumbers) {
        this.openGoalSerialNumbers = openGoalSerialNumbers;
    }

    public List<NodeIdentifier> getOpenGoalNodeIds() {
        return openGoalNodeIds;
    }

    public void setOpenGoalNodeIds(List<NodeIdentifier> openGoalNodeIds) {
        this.openGoalNodeIds = openGoalNodeIds;
    }

    @Override
    public String getMarkdown() {
        return String.format("## Applied macro %s%n```%n%s%n```", getMacro(), getInfo());
    }

    @Override
    public String getProofScriptRepresentation() {
        return String.format("macro %s;%n", getMacro());
    }

    @Override
    public void reapply(WindowUserInterfaceControl uic, Goal goal) throws Exception {
        ProofMacro macro = new ProofMacroApi().getMacro(getMacro());
        PosInOccurrence pio = getPos();
        if (macro != null) {
            if (!macro.canApplyTo(goal.node(), pio)) {
                throw new IllegalStateException("Macro not applicable");
            }

            try {
                macro.applyTo(uic, goal.node(), pio, uic);
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
    }
}
