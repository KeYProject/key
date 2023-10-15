package org.keyproject.key.api.data;

import de.uka.ilkd.key.pp.PositionTable;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
public record GoalText(PrintId id, String text, PositionTable table) {
}
