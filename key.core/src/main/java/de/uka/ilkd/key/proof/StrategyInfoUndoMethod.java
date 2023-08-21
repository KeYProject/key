/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.util.properties.Properties;


/**
 *
 * @author christoph
 */
public interface StrategyInfoUndoMethod {

    void undo(Properties strategyInfos);
}
