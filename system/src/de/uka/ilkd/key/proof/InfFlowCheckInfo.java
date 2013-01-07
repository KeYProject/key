/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.util.properties.Properties;


/**
 *
 * @author christoph
 */
public class InfFlowCheckInfo {
    public static final Properties.Property<Boolean> INF_FLOW_CHECK_PROPERTY =
            new Properties.Property<Boolean>(Boolean.class,
                                             "information flow check property");

    public static void set(Goal goal,
                           final boolean checkForInfFlow) {
        final boolean oldValue =
                goal.getStrategyInfo(INF_FLOW_CHECK_PROPERTY);
        StrategyInfoUndoMethod undo = new StrategyInfoUndoMethod() {

            @Override
            public void undo(Properties strategyInfos) {
                strategyInfos.put(INF_FLOW_CHECK_PROPERTY, oldValue);
            }
        };
        goal.addStrategyInfo(INF_FLOW_CHECK_PROPERTY, checkForInfFlow, undo);

    }

    public static boolean get(Goal goal) {
        return goal.getStrategyInfo(INF_FLOW_CHECK_PROPERTY);
    }

}
