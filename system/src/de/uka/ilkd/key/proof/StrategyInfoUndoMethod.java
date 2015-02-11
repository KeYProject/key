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
public interface StrategyInfoUndoMethod {

    void undo(Properties strategyInfos);
}
