package de.uka.ilkd.key.gui.interactionlog.model;

import de.uka.ilkd.key.gui.interactionlog.algo.InteractionVisitor;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import org.key_project.util.collection.ImmutableList;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlRootElement;
import javax.xml.bind.annotation.XmlTransient;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author weigl
 */
@XmlRootElement()
@XmlAccessorType(XmlAccessType.FIELD)
public final class MacroInteraction extends NodeInteraction {
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
        System.out.println("macro");
        this.macroName = macro.getScriptCommandName();
        this.pos = posInOcc;
        this.info = info.toString();

        ImmutableList<Goal> openGoals = info.getProof().openGoals();
        this.openGoalSerialNumbers = openGoals.stream().map(g -> g.node().serialNr()).collect(Collectors.toList());
        this.openGoalNodeIds = openGoals.stream().map(g -> NodeIdentifier.get(g.node())).collect(Collectors.toList());
    }

    @Override
    public String toString() {
        return macroName;
    }

    @Override
    public <T> T accept(InteractionVisitor<T> visitor) {
        return visitor.visit(this);
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
}
