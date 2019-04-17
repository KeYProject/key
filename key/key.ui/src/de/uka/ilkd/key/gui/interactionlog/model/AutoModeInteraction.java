package de.uka.ilkd.key.gui.interactionlog.model;

import de.uka.ilkd.key.gui.interactionlog.algo.InteractionVisitor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import org.key_project.util.collection.ImmutableList;

import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlRootElement;
import java.util.List;
import java.util.stream.Collectors;

@XmlRootElement()
@XmlAccessorType(XmlAccessType.FIELD)
public class AutoModeInteraction extends Interaction {
    private ApplyStrategyInfo info;

    private List<NodeIdentifier> initialNodeIds;
    private List<NodeIdentifier> openGoalNodeIds;

    public AutoModeInteraction() {
    }

    public AutoModeInteraction(List<Node> initialNodes, ApplyStrategyInfo info) {
        this.initialNodeIds = initialNodes.stream().map(NodeIdentifier::get).collect(Collectors.toList());

        ImmutableList<Goal> openGoals = info.getProof().openGoals();
        this.openGoalNodeIds = openGoals.stream().map(NodeIdentifier::get).collect(Collectors.toList());

        this.info = info;
    }

    @Override
    public <T> T accept(InteractionVisitor<T> visitor) {
        return visitor.visit(this);
    }

    public ApplyStrategyInfo getInfo() {
        return info;
    }

    public void setInfo(ApplyStrategyInfo info) {
        this.info = info;
    }

    public List<NodeIdentifier> getInitialNodeIds() {
        return initialNodeIds;
    }

    public void setInitialNodeIds(List<NodeIdentifier> initialNodeIds) {
        this.initialNodeIds = initialNodeIds;
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
