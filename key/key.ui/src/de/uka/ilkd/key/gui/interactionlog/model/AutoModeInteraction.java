package de.uka.ilkd.key.gui.interactionlog.model;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import org.key_project.util.collection.ImmutableList;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlRootElement;
import java.util.Date;
import java.util.List;
import java.util.stream.Collectors;

@XmlRootElement()
@XmlAccessorType(XmlAccessType.FIELD)
public class AutoModeInteraction extends Interaction {

    private ApplyStrategyInfo info;

    private List<Integer> initialNodeSerialNumbers;
    private List<NodeIdentifier> initialNodeIds;

    private List<Integer> openGoalSerialNumbers;
    private List<NodeIdentifier> openGoalNodeIds;
    private Date created = new Date();

    public AutoModeInteraction() {
    }

    public AutoModeInteraction(List<Node> initialNodes, ApplyStrategyInfo info) {
        this.initialNodeSerialNumbers = initialNodes.stream().map(Node::serialNr).collect(Collectors.toList());
        this.initialNodeIds = initialNodes.stream().map(NodeIdentifier::get).collect(Collectors.toList());

        ImmutableList<Goal> openGoals = info.getProof().openGoals();
        this.openGoalSerialNumbers = openGoals.stream().map(g -> g.node().serialNr()).collect(Collectors.toList());
        this.openGoalNodeIds = openGoals.stream().map(g -> NodeIdentifier.get(g.node())).collect(Collectors.toList());

        this.info = info;
    }

    @Override
    public String getProofScriptRepresentation(Services services) {
        StringBuilder sb = new StringBuilder("auto");

        initialNodeSerialNumbers.forEach(nr -> {
            sb.append("\n\t" + nr);
        });
        sb.append("\n\t" + info);

        sb.append(";");
        return sb.toString();
    }

    @Override
    public String getMarkdownText() {
        StringBuilder sb = new StringBuilder("---------\n");
        sb.append("## `auto`\n");
        sb.append("initial nodes:\n");

        initialNodeSerialNumbers.forEach( nr -> {
            sb.append("- ").append(nr).append("\n");
        });

        sb.append("\n");

        sb.append("```\n");
        sb.append(info);
        sb.append("\n```\n");

        return sb.toString();
    }

    public ApplyStrategyInfo getInfo() {
        return info;
    }

    public void setInfo(ApplyStrategyInfo info) {
        this.info = info;
    }

    public List<Integer> getInitialNodeSerialNumbers() {
        return initialNodeSerialNumbers;
    }

    public void setInitialNodeSerialNumbers(List<Integer> initialNodeSerialNumbers) {
        this.initialNodeSerialNumbers = initialNodeSerialNumbers;
    }

    public List<NodeIdentifier> getInitialNodeIds() {
        return initialNodeIds;
    }

    public void setInitialNodeIds(List<NodeIdentifier> initialNodeIds) {
        this.initialNodeIds = initialNodeIds;
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
    public String toString() {
        return "Auto Mode";
    }
}
