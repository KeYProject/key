package org.keyproject.key.api.internal;

import de.uka.ilkd.key.pp.InitialPositionTable;
import de.uka.ilkd.key.pp.PositionTable;
import de.uka.ilkd.key.proof.Node;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
public record NodeText(String text, InitialPositionTable table) {
}
