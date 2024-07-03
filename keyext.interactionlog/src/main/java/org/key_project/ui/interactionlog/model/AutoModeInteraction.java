/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package org.key_project.ui.interactionlog.model;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.List;
import java.util.stream.Collectors;
import javax.xml.bind.annotation.XmlAccessType;
import javax.xml.bind.annotation.XmlAccessorType;
import javax.xml.bind.annotation.XmlRootElement;

import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;

import org.key_project.ui.interactionlog.api.Interaction;
import org.key_project.util.collection.ImmutableList;

@XmlRootElement()
@XmlAccessorType(XmlAccessType.FIELD)
public class AutoModeInteraction extends Interaction {
    private static final long serialVersionUID = 3650173956594987169L;

    private ApplyStrategyInfo info;

    private List<NodeIdentifier> initialNodeIds;
    private List<NodeIdentifier> openGoalNodeIds;

    public AutoModeInteraction() {
    }

    public AutoModeInteraction(List<Node> initialNodes, ApplyStrategyInfo info) {
        this.initialNodeIds =
            initialNodes.stream().map(NodeIdentifier::get).collect(Collectors.toList());

        ImmutableList<Goal> openGoals = info.getProof().openGoals();
        this.openGoalNodeIds =
            openGoals.stream().map(NodeIdentifier::get).collect(Collectors.toList());

        this.info = info;
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

    @Override
    public String getMarkdown() {
        StringWriter sout = new StringWriter();
        PrintWriter out = new PrintWriter(sout);
        out.write("## Apply auto strategy%n%n");
        out.write("* Started on:");
        getInitialNodeIds().forEach(nr -> out.format("  * %s%n", nr));
        if (getOpenGoalNodeIds().isEmpty())
            out.format("* **Closed all goals**");
        else {
            out.format("* finished on:%n");
            getInitialNodeIds().forEach(nr -> out.format("  * %s%n", nr));
        }
        out.format("```%n%s%n```", getInfo());
        return sout.toString();
    }

    @Override
    public String getProofScriptRepresentation() {
        return ("auto;%n");
    }

    @Override
    public void reapply(WindowUserInterfaceControl uic, Goal goal) throws Exception {
        uic.getProofControl().startAutoMode(goal.proof(), goal.proof().openGoals(), uic);
    }
}
