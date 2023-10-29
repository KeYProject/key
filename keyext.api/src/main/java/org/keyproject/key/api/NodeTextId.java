package org.keyproject.key.api;

import org.keyproject.key.api.data.KeyIdentifications.NodeId;

/**
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
public record NodeTextId(NodeId nodeId, int nodeTextId) {
}
