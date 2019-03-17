package de.uka.ilkd.key.proof.runallproofs.performance;

import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

public class FunctionPerformanceData {

    private final Map<Integer, NodeData> nodeId2NodeData = new HashMap<>();
    private final File dataDir;
    private final DataRecordingTestFile dataRecordingTestFile;
    
    public int totalInvocations = 0;
    public long totalDuration = 0;

    public FunctionPerformanceData(File dataDir, DataRecordingTestFile dataRecordingTestFile) {
        this.dataRecordingTestFile = dataRecordingTestFile;
        this.dataDir = dataDir;
    }

    private NodeData getDataMapForGoal(Goal goal) {
        NodeData nodeData = nodeId2NodeData.get(goal.node().serialNr());
        if (nodeData == null) {
            nodeData = new NodeData(goal);
            nodeId2NodeData.put(nodeData.id, nodeData);
        }
        return nodeData;
    }

    public void addDurationToData(RuleApp app, Goal goal, long duration) {
        NodeData map = getDataMapForGoal(goal);
        String ruleName = app.rule().displayName();
        RuleData ruleData = map.ruleName2RuleData.get(ruleName);
        if (ruleData == null) {
            ruleData = new RuleData(duration);
            map.ruleName2RuleData.put(ruleName, ruleData);
        } else {
            ruleData.addDuration(duration);
        }
        
        totalInvocations++;
        totalDuration += duration;
    }

    private DataRecordingTable getTable(String ruleName, Map<String, DataRecordingTable> tables) {
        DataRecordingTable table = tables.get(ruleName);
        if (table == null) {
            try {
                File ruleDataLocation = new File(dataDir, ruleName + ".data");
                String[] columns = new String[]{"nodeId", "astCount", "proofTreeDepth", "numberInvocations", "         duration", "averageTimePerInvocation"};
                String description = "Profiling data for rule " + ruleName;
                table = new DataRecordingTable(ruleDataLocation, columns, description);
                tables.put(ruleName, table);
                table.writeComment("# " + dataRecordingTestFile.getKeYFile().getName() + "\n");
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
        return table;
    }

    public void updateData() {
        Map<String, DataRecordingTable> tables = new HashMap<>();
        Collection<NodeData> nodeData = nodeId2NodeData.values();
        for (NodeData node : nodeData) {
            for (Entry<String, RuleData> entry : node.ruleName2RuleData.entrySet()) {
                RuleData ruleData = entry.getValue();
                int invocations = ruleData.numberInvocations;
                long duration = ruleData.duration;
                getTable(entry.getKey(), tables).writeRow(node.id, node.astDepth, node.proofTreeDepth,
                        invocations, duration, ((double) duration) / ((double) invocations));
            }
        }
        for (DataRecordingTable table : tables.values()) {
            try {
                table.close();
            } catch (Exception e) {
                throw new RuntimeException(e);
            }
        }
    }

}
